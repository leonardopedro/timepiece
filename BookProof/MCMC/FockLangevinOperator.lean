import Mathlib
import BookProof.MCMC.UnadjustedPCNGap
import BookProof.Toolbox.ChapterFockFieldPerturbation

/-!
# Chapter FockLangevinOperator — the drift as a finite-band hopping matrix

Plan: `pcnl.md`, Module 3.  §2.2 writes the pCNL transition operator as
`P_pCNL = P₀ + K_drift + K_reject`, where `P₀` is diagonal (`ρ^N`) and the drift is the
polynomial `−½β²∇Φ`.  In the Hermite/Fock basis a polynomial becomes a **finite combination of
ladder words** in `(a_j, a_j†)`, and a ladder word moves the occupation numbers of only the
modes it touches, by one per letter — so the drift is a *finite-band* matrix: a monomial of
degree `k` hops the total degree `N = ∑ i, nᵢ` by at most `k`.

This chapter makes that structural fact precise on the Gauss–polynomial core
`CoreCoeff d = (Fin d → ℕ) →₀ ℂ` of `BookProof.ReferenceGap`, whose degree function
`natDeg` and pCN weights `pcnWeight` are those of `BookProof.MCMC.UnadjustedPCN`.

## Contents

* `raiseIdx`, `lowerIdx`, `stepIdx` — `a_j†` and `a_j` as operations on occupations;
  `natDeg_raiseIdx` (`N ↦ N + 1`) and `natDeg_lowerIdx_le` (`N ↦ ≤ N`);
* `stepAmp` — the Hermite/Fock amplitude `√(n_j + 1)` of a raising step and `√(n_j)` of a
  lowering step, and `stepAmp_norm_le` — **on the degree-`≤ N` sector every step amplitude is at
  most `√(N + 1)`**, the growth the relative-bound argument of the plan's Module 3 needs;
* `hopStep`, `hopWord`, `driftOp` — one ladder step, a word of steps, and a finite family of
  words (the drift monomials) acting on the core;
* **`hopWord_band`** and **`driftOp_band`** — the finite-band property: a word of length `k` maps
  the sector `{N ≤ N₀}` into `{N ≤ N₀ + k}`, and a family of words of length `≤ K` into
  `{N ≤ N₀ + K}`;
* `numberOp` — the diagonal Fock number operator `N` on the core, whose support is unchanged, so
  that `numberOp + driftOp W` is the `pcnlHamiltonian` shape of the plan's milestone;
* **§5, the `ε`-regularized relative form bound** — `corePair` (the `ℓ²` pairing), `numberForm`
  (`⟪c, N c⟫`), `driftOpCoeff` (`K_drift = −Σ_j b_j ∂_j` with `∂_j = (a_j − a_j†)/√2` as a hopping
  operator), and  **`DriftFormBound`**, the plan's Module 3 target stated as a `Prop` with the
  plan's constant;
* **§6, the same bound proved** — `driftField` (the drift on the corpus Fock space,
  `creVec − annVec`), `abs_re_inner_driftField_le` (its `N^{1/2}` estimate) and
  **`driftField_relative_form_bound`**:
  relative bound zero against the number form, as a theorem, reusing
  `BookProof.FockFieldPerturbation`;
* **§7, the index identification** — `idxEquiv` (occupation vectors on `d` modes *are* finite
  multisets) and `natDeg_idxEquiv` (the grading is the particle number);
* **§8, the `Fin d` sector** — the other half of the identification: `reindex`,
  `sum_sq_reindex` and `numberForm_reindex` move the core `ℓ²` isometrically onto configuration
  vectors on multisets; `sectorVec` and `l2norm_sectorVec` embed a `Fin d` coupling as a
  one-particle vector on the first `d` modes, and `driftField_sector_relative_form_bound` is
  Module 3's bound with the `Fin d` constants; `InSector`, `numberQuad_eq_sum_fin` and
  `InSector.driftField` are the corresponding sector of the Fock model and its invariance under
  the drift.

## Honest boundary

What is proved is the *band structure* — the combinatorial content of "the drift is a
finite-band hopping matrix" — together with the size of the hopping amplitudes.  Three inputs of
the plan's Module 3 are **not** proved: that a given polynomial potential `Φ` is exactly a sum of
these ladder words with the stated coefficients (that is the Hermite expansion of `∇Φ`, which
needs the multiplication law `x_j = (a_j + a_j†)/√2` and the Mehler measure); the relative form
bound that makes `K_drift` a bounded perturbation of `P₀`; and the Metropolis step `K_reject`.
The rejection filter is not a finite-band operator at all — it is a multiplication operator — so
nothing here says anything about it.

The relative form bound is now **stated** in §5 (`DriftFormBound`) with the plan's constant
`B²d/(2δ) + Bd`, over the same core and the same ladder words as the rest of the file — a `def`
returning a `Prop`, so the development stays free of `sorry`.  What a proof would still need is the
Hermite-expansion input above plus three analytic steps that are themselves routine on the core:
the adjoint pairing `⟪c, a_j c⟫`, Cauchy–Schwarz in the `ℓ²` pairing, and the oscillator identity
`Σ_j (‖a_j c‖² + ‖a_j† c‖²) = 2⟪c, N c⟫ + d‖c‖²`.  Those three are *not* formalized here; the
statement below is a target, and is marked as one.
-/

noncomputable section

namespace BookProof.MCMC.FockLangevin

open Finset
open BookProof.ReferenceGap
open BookProof.MCMC.UnadjustedPCN

variable {d : ℕ}

/-! ## 1. Ladder steps on occupations -/

/-- `a_j†`: raise the occupation of mode `j` by one. -/
def raiseIdx (j : Fin d) (n : Fin d → ℕ) : Fin d → ℕ := Function.update n j (n j + 1)

/-- `a_j`: lower the occupation of mode `j` by one, saturating at `0`. -/
def lowerIdx (j : Fin d) (n : Fin d → ℕ) : Fin d → ℕ := Function.update n j (n j - 1)

/-- The occupation shift of one ladder letter: `true` raises (creation), `false` lowers
(annihilation). -/
def stepIdx (b : Bool) (j : Fin d) (n : Fin d → ℕ) : Fin d → ℕ :=
  if b then raiseIdx j n else lowerIdx j n

/-- Splitting the total degree at one mode. -/
theorem sum_erase (f : Fin d → ℕ) (j : Fin d) :
    f j + ∑ i ∈ Finset.univ.erase j, f i = ∑ i, f i :=
  Finset.add_sum_erase _ f (Finset.mem_univ j)

theorem sum_erase_update (n : Fin d → ℕ) (j : Fin d) (v : ℕ) :
    ∑ i ∈ Finset.univ.erase j, Function.update n j v i = ∑ i ∈ Finset.univ.erase j, n i :=
  Finset.sum_congr rfl fun i hi => by simp [Finset.ne_of_mem_erase hi]

/-- **Creation raises the total degree by one.** -/
theorem natDeg_raiseIdx (j : Fin d) (n : Fin d → ℕ) : natDeg (raiseIdx j n) = natDeg n + 1 := by
  have h1 := sum_erase n j
  have h2 := sum_erase (Function.update n j (n j + 1)) j
  have h3 := sum_erase_update n j (n j + 1)
  have h4 : Function.update n j (n j + 1) j = n j + 1 := by simp
  unfold natDeg raiseIdx
  omega

/-- **Annihilation does not raise the total degree.** -/
theorem natDeg_lowerIdx_le (j : Fin d) (n : Fin d → ℕ) : natDeg (lowerIdx j n) ≤ natDeg n := by
  have h1 := sum_erase n j
  have h2 := sum_erase (Function.update n j (n j - 1)) j
  have h3 := sum_erase_update n j (n j - 1)
  have h4 : Function.update n j (n j - 1) j = n j - 1 := by simp
  unfold natDeg lowerIdx
  omega

/-- The degree change of one ladder letter, in the two cases. -/
theorem natDeg_stepIdx_raise (j : Fin d) (n : Fin d → ℕ) :
    natDeg (stepIdx true j n) = natDeg n + 1 := natDeg_raiseIdx j n

theorem natDeg_stepIdx_lower (j : Fin d) (n : Fin d → ℕ) :
    natDeg (stepIdx false j n) ≤ natDeg n := natDeg_lowerIdx_le j n

/-- Every ladder letter changes the total degree by at most one. -/
theorem natDeg_stepIdx_le (b : Bool) (j : Fin d) (n : Fin d → ℕ) :
    natDeg (stepIdx b j n) ≤ natDeg n + 1 := by
  cases b with
  | true => rw [natDeg_stepIdx_raise]
  | false => have := natDeg_stepIdx_lower j n; omega

/-! ## 2. The step amplitudes -/

/-- The Hermite/Fock matrix element of one ladder letter: `√(n_j + 1)` for `a_j†`, `√(n_j)` for
`a_j`. -/
def stepAmp (b : Bool) (j : Fin d) (n : Fin d → ℕ) : ℂ :=
  if b then ((Real.sqrt (n j + 1) : ℝ) : ℂ) else ((Real.sqrt (n j) : ℝ) : ℂ)

theorem stepAmp_raise (j : Fin d) (n : Fin d → ℕ) :
    stepAmp true j n = ((Real.sqrt (n j + 1) : ℝ) : ℂ) := rfl

theorem stepAmp_lower (j : Fin d) (n : Fin d → ℕ) :
    stepAmp false j n = ((Real.sqrt (n j) : ℝ) : ℂ) := rfl

/-- **The step amplitude is `≤ √(N + 1)` on the degree-`≤ N` sector.**  This is the size estimate
the plan's relative-bound argument needs: `K_drift` grows only like the square root of the
background occupation. -/
theorem stepAmp_norm_le (b : Bool) (j : Fin d) {n : Fin d → ℕ} {N : ℕ} (hn : natDeg n ≤ N) :
    ‖stepAmp b j n‖ ≤ Real.sqrt ((N : ℝ) + 1) := by
  have hle : n j ≤ N := le_trans (Finset.single_le_sum (f := n) (fun i _ => Nat.zero_le _)
    (Finset.mem_univ j)) hn
  have hleR : (n j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle
  cases b with
  | true =>
    rw [stepAmp_raise, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (by linarith)
  | false =>
    rw [stepAmp_lower, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (by linarith)

/-! ## 3. The hopping operators -/

/-- **One ladder step on the core**, with its amplitude: the monomial `a_j†` or `a_j` acting on a
coefficient family. -/
def hopStep (p : Fin d × Bool) (c : CoreCoeff d) : CoreCoeff d :=
  c.sum fun n a => Finsupp.single (stepIdx p.2 p.1 n) (stepAmp p.2 p.1 n * a)

/-- Membership in the support of a one-step hop: the new index is a ladder shift of an old one. -/
theorem mem_support_hopStep {p : Fin d × Bool} {c : CoreCoeff d} {m : Fin d → ℕ}
    (hm : m ∈ (hopStep p c).support) : ∃ n ∈ c.support, m = stepIdx p.2 p.1 n := by
  unfold hopStep at hm
  have hsub : (c.sum fun n a =>
      Finsupp.single (stepIdx p.2 p.1 n) (stepAmp p.2 p.1 n * a)).support ⊆
      c.support.biUnion (fun n => (Finsupp.single (stepIdx p.2 p.1 n)
        (stepAmp p.2 p.1 n * c n)).support) := Finsupp.support_sum
  obtain ⟨n, hn, hmn⟩ := Finset.mem_biUnion.mp (hsub hm)
  have hm' : m = stepIdx p.2 p.1 n := by
    simpa using Finsupp.support_single_subset hmn
  exact ⟨n, hn, hm'⟩

/-- **The one-step band**: a ladder letter maps the sector `{N ≤ N₀}` into `{N ≤ N₀ + 1}`. -/
theorem hopStep_band {p : Fin d × Bool} {c : CoreCoeff d} {N : ℕ}
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) {m : Fin d → ℕ} (hm : m ∈ (hopStep p c).support) :
    natDeg m ≤ N + 1 := by
  obtain ⟨n, hn, rfl⟩ := mem_support_hopStep hm
  have hnN : natDeg n ≤ N := hc n hn
  exact le_trans (natDeg_stepIdx_le p.2 p.1 n) (by omega)

/-- A **word** of ladder letters, applied left to right. -/
def hopWord : List (Fin d × Bool) → CoreCoeff d → CoreCoeff d
  | [], c => c
  | p :: w, c => hopWord w (hopStep p c)

/-- **The finite-band property of a ladder word**: a word of length `k` maps the sector
`{N ≤ N₀}` into `{N ≤ N₀ + k}`.  This is `pcnl.md` §2.2's "finite-band hopping matrix". -/
theorem hopWord_band (w : List (Fin d × Bool)) :
    ∀ (c : CoreCoeff d) (N : ℕ), (∀ n ∈ c.support, natDeg n ≤ N) →
      ∀ m ∈ (hopWord w c).support, natDeg m ≤ N + w.length := by
  induction w with
  | nil =>
    intro c N hc m hm
    rw [hopWord] at hm
    have := hc m hm
    simpa using this
  | cons p w ih =>
    intro c N hc m hm
    rw [hopWord] at hm
    have hstep : ∀ n ∈ (hopStep p c).support, natDeg n ≤ N + 1 := fun n hn =>
      hopStep_band hc hn
    have := ih (hopStep p c) (N + 1) hstep m hm
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- **The drift operator**: a finite family of ladder words (one per monomial of the potential),
summed.  This is the plan's `K_drift`. -/
def driftOp : List (List (Fin d × Bool)) → CoreCoeff d → CoreCoeff d
  | [], _ => 0
  | w :: ws, c => hopWord w c + driftOp ws c

/-- **The drift is finite-band.**  If every monomial has degree at most `K`, then `K_drift` maps
the sector `{N ≤ N₀}` into `{N ≤ N₀ + K}`: applying the drift can change the occupation only by
a bounded amount, which is the structural fact behind the plan's relative bound. -/
theorem driftOp_band (words : List (List (Fin d × Bool))) {K : ℕ}
    (hK : ∀ w ∈ words, w.length ≤ K) (c : CoreCoeff d) {N : ℕ}
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) {m : Fin d → ℕ}
    (hm : m ∈ (driftOp words c).support) : natDeg m ≤ N + K := by
  induction words with
  | nil => simp [driftOp] at hm
  | cons w ws ih =>
    rw [driftOp] at hm
    have hw : w.length ≤ K := hK w (List.mem_cons_self)
    have hws : ∀ w' ∈ ws, w'.length ≤ K := fun w' hw' => hK w' (List.mem_cons_of_mem _ hw')
    have hmem := Finset.mem_union.mp (Finsupp.support_add hm)
    rcases hmem with h1 | h2
    · exact le_trans (hopWord_band w c N hc m h1) (by omega)
    · exact ih hws h2

/-! ## 4. The number operator, and the pCNL shape -/

/-- The Fock number operator `N = ∑ a_j† a_j` on the core: diagonal, with eigenvalue `natDeg n`. -/
def numberOp (c : CoreCoeff d) : CoreCoeff d :=
  c.sum fun n a => Finsupp.single n ((natDeg n : ℂ) * a)

/-- The number operator is diagonal, hence does not move the support. -/
theorem mem_support_numberOp {c : CoreCoeff d} {m : Fin d → ℕ}
    (hm : m ∈ (numberOp c).support) : m ∈ c.support := by
  unfold numberOp at hm
  have hsub : (c.sum fun n a => Finsupp.single n ((natDeg n : ℂ) * a)).support ⊆
      c.support := by
    refine Finset.Subset.trans Finsupp.support_sum ?_
    intro x hx
    obtain ⟨n, hn, hxn⟩ := Finset.mem_biUnion.mp hx
    have hxeq : x = n := by simpa using Finsupp.support_single_subset hxn
    rwa [hxeq]
  exact hsub hm

/-- `pcnl.md` §2.2's operator shape on the core: the sum of the diagonal `P₀`/number part and the
finite-band drift.  (`P₀` itself is the diagonal contraction `pcnWeight` of
`BookProof.MCMC.UnadjustedPCN`; the Metropolis filter is a multiplication operator and is outside
this model.) -/
def pcnlHamiltonian (words : List (List (Fin d × Bool))) (c : CoreCoeff d) : CoreCoeff d :=
  numberOp c + driftOp words c

/-- **The pCNL Hamiltonian is finite-band around the diagonal.**  Its drift part moves the degree
by at most `K`, so the operator has bandwidth `K` in the occupation grading — the reason a
truncation at degree `N₀` couples only to degrees `≤ N₀ + K`. -/
theorem pcnlHamiltonian_band (words : List (List (Fin d × Bool))) {K : ℕ}
    (hK : ∀ w ∈ words, w.length ≤ K) (c : CoreCoeff d) {N : ℕ}
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) {m : Fin d → ℕ}
    (hm : m ∈ (pcnlHamiltonian words c).support) : natDeg m ≤ N + K := by
  rw [pcnlHamiltonian] at hm
  rcases Finset.mem_union.mp (Finsupp.support_add hm) with h1 | h2
  · exact le_trans (hc m (mem_support_numberOp h1)) (by omega)
  · exact driftOp_band words hK c hc h2

/-! ## 5. The `ε`-regularized relative form bound (Module 3 target) -/

/-- The `ℓ²` pairing `⟪c, c'⟫ = ∑ₙ c n · conj (c' n)`, summed over the union of the two supports:
both are finitely supported, so no completion of the core is needed. -/
def corePair (c c' : CoreCoeff d) : ℂ :=
  ∑ n ∈ c.support ∪ c'.support, c n * star (c' n)

/-- The quadratic form of the number operator, `⟪c, N c⟫ = ∑ₙ (∑ᵢ nᵢ)·‖c n‖²` — the object that
`‖N^{1/2}ψ‖²` of the plan is, read on the core. -/
def numberForm (c : CoreCoeff d) : ℝ :=
  ∑ n ∈ c.support, (natDeg n : ℝ) * ‖c n‖ ^ 2

theorem numberForm_nonneg (c : CoreCoeff d) : 0 ≤ numberForm c :=
  Finset.sum_nonneg fun n _ => mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- `1/√2`, the normalization in `∂_j = (a_j − a_j†)/√2`. -/
def invSqrtTwo : ℝ := 1 / Real.sqrt 2

/-- **The drift as a hopping operator with coefficients**, `K_drift = −∑_j b_j ∂_j`:
`∑_j [ (−b_j/√2)·a_j + (b_j/√2)·a_j† ]`, each letter being a `hopStep`.  The plan's `K_drift` is
this operator with `b_j = (β²σ²/2)·∂_jΦ_ε`, so `|b_j| ≤ B` with `B = β²σ²M_ε/2`. -/
def driftOpCoeff (b : Fin d → ℝ) (c : CoreCoeff d) : CoreCoeff d :=
  Finset.univ.sum fun j : Fin d =>
    (((-(b j)) * invSqrtTwo : ℝ) : ℂ) • hopStep (j, false) c +
      (((b j) * invSqrtTwo : ℝ) : ℂ) • hopStep (j, true) c

/-- **Module 3's target: the `ε`-regularized relative form bound for `K_drift`.**

For every coefficient family `b : Fin d → ℝ` with `|b j| ≤ B`, every `δ > 0` and every core state
`c`,

`‖⟪c, K_drift c⟫‖ ≤ δ·⟪c, N c⟫ + (B²·d/(2δ) + B·d)·‖c‖²`,

with `d` the number of modes (the plan's `P`) and `B = β²σ²M_ε/2`, `M_ε = K/ε` the gradient bound of
the `ε`-regularized architecture.  `δ` is arbitrary, so the relative bound is **zero**: `K_drift` is
infinitesimally form-small with respect to `N`, which is what makes `N + K_drift` self-adjoint and
bounded below by KLMN.

The plan's constant is reproduced by the chain
`|⟪c, K c⟫| ≤ (B/√2)·‖c‖·∑_j (‖a_j c‖ + ‖a_j† c‖)`, then
`≤ B·√d·‖c‖·√(2⟪c,Nc⟫ + d‖c‖²)`, then `√(x + y) ≤ √x + √y` and `2ab ≤ δa² + b²/δ`; the
oscillator identity
`Σ_j (‖a_j c‖² + ‖a_j† c‖²) = 2⟪c, N c⟫ + d·‖c‖²` is the only input that is not bookkeeping.
**This is a target, not a theorem**: it is a `Prop`, and the Hermite expansion identifying `∇Φ_ε`
with these ladder coefficients is the missing input (see the module's honest boundary).  What it
pins down — and what the plan needs — is that the only `ε`-dependence enters through `B`, and
hence quadratically as `ε⁻²`, which is why the bound certifies semiboundedness and cannot supply
the gap. -/
def DriftFormBound (B : ℝ) (b : Fin d → ℝ) : Prop :=
  (∀ j, |b j| ≤ B) →
    ∀ (δ : ℝ), 0 < δ →
      ∀ c : CoreCoeff d,
        ‖corePair c (driftOpCoeff b c)‖ ≤
          δ * numberForm c + (B ^ 2 * (d : ℝ) / (2 * δ) + B * (d : ℝ)) * coreNormSq c

/-! ## 6. The same bound as a theorem, in the corpus Fock model

`DriftFormBound` above is stated on the coefficient core `CoreCoeff d`, where it remains a target.
The corpus already carries a Fock model with the analytic machinery attached —
`BookProof.FockFieldPerturbation` proves the relative form bound for the field operator
`Φ(f) = a†(f) + a(f)` against the number form.  The plan's drift is the *difference*
`K_drift = Σⱼ (bⱼ/√2)(a†ⱼ − aⱼ) = creVec f − annVec f` with `f = b/√2`, so the same estimate gives
the bound with relative bound zero, and here it is a theorem rather than a statement.

What is still a modelling step — and it is the same *kind* of step that `cftproof.md` item 3
records for the OS identity — is the identification of the two models: `CoreCoeff d` indexes by
occupation *vectors* `Fin d → ℕ`, the Fock toolbox by finite *multisets* of modes (`Conf →₀ ℂ`).
Nothing in the corpus transports a bound along that equivalence, so the CoreCoeff statement stays
a target and this section proves the Fock-model twin.
-/

open BookProof.FockFieldPerturbation
open BookProof.FockSecondQuantization

/-- **The drift on the corpus Fock space**: `Σⱼ (fⱼ a†ⱼ + conj fⱼ aⱼ)` is `creVec f + annVec f`;
for a *real* coefficient family the plan's `−Σⱼ bⱼ ∂ⱼ` is the difference `creVec f − annVec f` with
`f = b/√2`. -/
def driftField (f : ℕ →₀ ℂ) : FockAlg →ₗ[ℂ] FockAlg := creVec f - annVec f

theorem driftField_apply (f : ℕ →₀ ℂ) (u : FockAlg) :
    driftField f u = creVec f u - annVec f u := rfl

/-- **The `N^{1/2}` estimate for the drift**, the difference form of
`abs_re_inner_fieldVec_le`: `|Re⟪u, K u⟫| ≤ 2‖f‖·⟪u, N u⟫^{1/2}·‖u‖`. -/
theorem abs_re_inner_driftField_le (f : ℕ →₀ ℂ) (u : FockAlg) :
    |(inner ℂ (toLp u) (toLp (driftField f u)) : ℂ).re|
      ≤ 2 * l2norm f * Real.sqrt (numberQuad u) * ‖toLp u‖ := by
  have hsplit : (inner ℂ (toLp u) (toLp (driftField f u)) : ℂ)
      = inner ℂ (toLp u) (toLp (creVec f u)) - inner ℂ (toLp u) (toLp (annVec f u)) := by
    have hsub : toLp (driftField f u) = toLp (creVec f u) - toLp (annVec f u) := by
      have hs := map_sub toLpL (creVec f u) (annVec f u)
      simpa only [toLpL_apply, driftField_apply] using hs
    rw [hsub, inner_sub_right]
  have hbound : ‖toLp (annVec f u)‖ * ‖toLp u‖
      ≤ l2norm f * Real.sqrt (numberQuad u) * ‖toLp u‖ :=
    mul_le_mul_of_nonneg_right (norm_annVec_le f u) (norm_nonneg _)
  have h1 : |((inner ℂ (toLp u) (toLp (creVec f u)) : ℂ)).re|
      ≤ l2norm f * Real.sqrt (numberQuad u) * ‖toLp u‖ := by
    rw [inner_creVec_annVec]
    calc |(inner ℂ (toLp (annVec f u)) (toLp u) : ℂ).re|
        ≤ ‖(inner ℂ (toLp (annVec f u)) (toLp u) : ℂ)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖toLp (annVec f u)‖ * ‖toLp u‖ := norm_inner_le_norm _ _
      _ ≤ _ := hbound
  have h2 : |((inner ℂ (toLp u) (toLp (annVec f u)) : ℂ)).re|
      ≤ l2norm f * Real.sqrt (numberQuad u) * ‖toLp u‖ := by
    calc |(inner ℂ (toLp u) (toLp (annVec f u)) : ℂ).re|
        ≤ ‖(inner ℂ (toLp u) (toLp (annVec f u)) : ℂ)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖toLp u‖ * ‖toLp (annVec f u)‖ := norm_inner_le_norm _ _
      _ = ‖toLp (annVec f u)‖ * ‖toLp u‖ := mul_comm _ _
      _ ≤ _ := hbound
  rw [hsplit, Complex.sub_re]
  calc |(inner ℂ (toLp u) (toLp (creVec f u)) : ℂ).re
          - (inner ℂ (toLp u) (toLp (annVec f u)) : ℂ).re|
      ≤ |(inner ℂ (toLp u) (toLp (creVec f u)) : ℂ).re|
        + |(inner ℂ (toLp u) (toLp (annVec f u)) : ℂ).re| := by
        simpa [sub_eq_add_neg] using abs_add_le (a := (inner ℂ (toLp u) (toLp (creVec f u)) : ℂ).re)
          (b := -((inner ℂ (toLp u) (toLp (annVec f u)) : ℂ).re))
    _ ≤ 2 * l2norm f * Real.sqrt (numberQuad u) * ‖toLp u‖ := by linarith

/-- **Module 3's bound as a theorem (Fock model).**  For every coupling vector `f` and every
`t > 0`,

`|Re⟪u, K_drift u⟫| ≤ t·⟪u, N u⟫ + (‖f‖²/t)·‖u‖²`,

so the relative bound is zero: `K_drift` is infinitesimally form-small with respect to the number
operator.  `t` is the plan's `δ` and `‖f‖²/t` its `C_δ`. -/
theorem driftField_relative_form_bound (f : ℕ →₀ ℂ) {t : ℝ} (ht : 0 < t) (u : FockAlg) :
    |(inner ℂ (toLp u) (toLp (driftField f u)) : ℂ).re|
      ≤ t * numberQuad u + l2norm f ^ 2 / t * ‖toLp u‖ ^ 2 := by
  have h1 := abs_re_inner_driftField_le f u
  have h2 := two_mul_sqrt_le (c := l2norm f) (n := ‖toLp u‖) (N := numberQuad u) (t := t)
    (numberQuad_nonneg u) ht
  linarith

/-! ## 7. The index-level model identification: occupation vectors are multisets

`CoreCoeff d` indexes by occupation *vectors* `Fin d → ℕ`; the corpus Fock toolbox
(`BookProof.FockSecondQuantization`) indexes by finite *multisets* of modes.  On a finite mode set
the two are the same data — `Fin d` is finite, so every `Fin d → ℕ` is finitely supported, and
`Finsupp.equivFunOnFinite` is the bijection.  This section records the bijection and checks that
the degree grading (§1's `natDeg`, the `N` of the number operator) is read through it, so the
sector structure of §4's band lemmas is the sector structure of the Fock model.

Section 8 carries out the rest: the `ℓ²` reindexing along `idxEquiv` (`reindex`,
`sum_sq_reindex`, `numberForm_reindex`), and the restriction to the `Fin d` mode sector
(`sectorVec`, `l2norm_sectorVec`, `driftField_sector_relative_form_bound`, `InSector`).  What is
still *not* claimed is that §5's `DriftFormBound` follows — see the note in §8. -/

/-- **Occupation vectors on `d` modes are finite multisets of modes.** -/
def idxEquiv (d : ℕ) : (Fin d → ℕ) ≃ (Fin d →₀ ℕ) :=
  Finsupp.equivFunOnFinite.symm

@[simp] theorem idxEquiv_apply (n : Fin d → ℕ) (i : Fin d) : idxEquiv d n i = n i := rfl

@[simp] theorem idxEquiv_symm_apply (s : Fin d →₀ ℕ) (i : Fin d) : (idxEquiv d).symm s i = s i :=
  rfl

/-- **The degree is the particle number of the multiset**: `N` on an occupation vector is the total
count of the corresponding multiset, so the grading is the same on both sides of `idxEquiv`. -/
theorem natDeg_idxEquiv (n : Fin d → ℕ) :
    (idxEquiv d n).sum (fun _ m => m) = natDeg n := by
  rw [Finsupp.sum_fintype]
  · rfl
  · intro i
    rfl

/-! ## 8. The `Fin d` mode sector: the `ℓ²` reindexing and the sector restriction

§7 identified the *indices* — an occupation vector on `d` modes is a finite multiset of modes.
This section completes the identification on the two objects the relative bound is stated for.

**The states.**  `reindex` reads a core state `CoreCoeff d` as a configuration vector on
multisets.  `sum_sq_reindex` says it is an isometry of the core `ℓ²`, and `numberForm_reindex`
says it carries the core's number form `∑ n, N(n)‖c n‖²` to `∑ s, (s.sum id)‖ĉ s‖²` — the shape of
`⟪u, N u⟫` in the corpus Fock model.

**The coupling.**  The toolbox's modes are all of `ℕ`; this chapter's are `Fin d`.
`sectorVec` embeds a `Fin d` coupling as a one-particle vector supported on `{0, …, d−1}`,
`l2norm_sectorVec` reindexes its `ℓ²` norm, and `driftField_sector_relative_form_bound` is
Module 3's bound with the `Fin d` constants `∑ᵢ‖bᵢ‖²` and the `d`-mode sum.

**The sector.**  `InSector` is the subspace of states whose excited modes are all in the first
`d`; `annA_eq_zero_of_sector` kills the modes beyond it, `numberQuad_eq_sum_fin` reindexes the
number form onto `Fin d`, and `InSector.driftField` shows a `Fin d` coupling cannot carry a state
out of the sector.

What this section deliberately does **not** claim is that `DriftFormBound` follows.  That needs
two more steps, and they are of different kinds: (i) the real coupling `b : Fin d → ℝ` of
`driftOpCoeff` is the field `driftField (sectorVec (b : Fin d → ℂ))` only after the Hermite
expansion `∂_j = (a_j − a_j†)/√2` of the potential — the missing input named in the module's
honest boundary; (ii) `numberQuad` is the form of the number operator on the *configuration*
space, whereas `numberForm` is its form on the core, so transporting the estimate from one to the
other is the reindexing `sum_sq_reindex` / `numberForm_reindex` *plus* the identification of the
quadratic forms, again via the Hermite basis.  What is now fixed is the model: the constants,
the grading, the sector and the `ℓ²` structures agree. -/

section Sector

/-- **The `ℓ²` reindexing of the core**: a core state, read as a configuration vector on the
multisets of the `d` modes (`idxEquiv`). -/
def reindex (c : CoreCoeff d) : (Fin d →₀ ℕ) →₀ ℂ := Finsupp.mapDomain (idxEquiv d) c

/-- The degree of a multiset of modes: its total particle number. -/
def confDeg (s : Fin d →₀ ℕ) : ℕ := s.sum fun _ m => m

theorem confDeg_idxEquiv (n : Fin d → ℕ) : confDeg (idxEquiv d n) = natDeg n := natDeg_idxEquiv n

@[simp] theorem reindex_apply (c : CoreCoeff d) (n : Fin d → ℕ) :
    reindex c (idxEquiv d n) = c n :=
  Finsupp.mapDomain_apply (idxEquiv d).injective c n

theorem support_reindex (c : CoreCoeff d) :
    (reindex c).support = c.support.image (idxEquiv d) :=
  Finsupp.mapDomain_support_of_injective (idxEquiv d).injective c

/-- **The reindexing is an isometry of the core `ℓ²`**: the squared norm of a core state,
computed in the multiset indexing, is `coreNormSq`. -/
theorem sum_sq_reindex (c : CoreCoeff d) :
    ∑ s ∈ (reindex c).support, ‖reindex c s‖ ^ 2 = coreNormSq c := by
  rw [support_reindex, coreNormSq, Finset.sum_image]
  · exact Finset.sum_congr rfl fun n _ => by rw [reindex_apply]
  · intro x _ y _ hxy
    exact (idxEquiv d).injective hxy

/-- **The number form is the multiset form.**  Under the reindexing, `numberForm` becomes
`∑ s, (∂eg s)·‖ĉ s‖²` — the degree weight read off the multiset, which is the shape of the Fock
number form `⟪u, N u⟫`. -/
theorem numberForm_reindex (c : CoreCoeff d) :
    ∑ s ∈ (reindex c).support, ((confDeg s : ℕ) : ℝ) * ‖reindex c s‖ ^ 2 = numberForm c := by
  rw [support_reindex, numberForm, Finset.sum_image]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [reindex_apply, confDeg_idxEquiv]
  · intro x _ y _ hxy
    exact (idxEquiv d).injective hxy

/-- **A `Fin d` coupling as a one-particle vector of the Fock model**, supported on the modes
`{0, …, d−1}`. -/
def sectorVec (b : Fin d → ℂ) : ℕ →₀ ℂ :=
  Finsupp.onFinset (Finset.range d) (fun j => if h : j < d then b ⟨j, h⟩ else 0)
    (fun j hj => by
      by_contra hmem
      have hnd : ¬ j < d := by simpa [Finset.mem_range] using hmem
      exact hj (by simp [hnd]))

@[simp] theorem sectorVec_apply (b : Fin d → ℂ) (j : ℕ) :
    sectorVec b j = if h : j < d then b ⟨j, h⟩ else 0 := by
  simp [sectorVec]

theorem sectorVec_apply_of_lt (b : Fin d → ℂ) {j : ℕ} (hj : j < d) :
    sectorVec b j = b ⟨j, hj⟩ := by
  rw [sectorVec_apply, dif_pos hj]

theorem sectorVec_apply_of_ge (b : Fin d → ℂ) {j : ℕ} (hj : d ≤ j) : sectorVec b j = 0 := by
  rw [sectorVec_apply, dif_neg (by omega)]

theorem support_sectorVec (b : Fin d → ℂ) : (sectorVec b).support ⊆ Finset.range d :=
  Finsupp.support_onFinset_subset

/-- **The `ℓ²` norm of a `Fin d` coupling**: the one-particle vector carries exactly the
coefficient norm `√(∑ᵢ‖bᵢ‖²)`. -/
theorem sum_sq_sectorVec (b : Fin d → ℂ) :
    ∑ j ∈ (sectorVec b).support, ‖sectorVec b j‖ ^ 2 = ∑ i : Fin d, ‖b i‖ ^ 2 := by
  rw [Finset.sum_subset (support_sectorVec b) (fun j _ hmem => by
    rw [Finsupp.notMem_support_iff.mp hmem, norm_zero]
    simp)]
  rw [Finset.sum_range (fun j => ‖sectorVec b j‖ ^ 2)]
  exact Finset.sum_congr rfl fun i _ => by rw [sectorVec_apply_of_lt b i.isLt]

theorem l2norm_sectorVec (b : Fin d → ℂ) :
    l2norm (sectorVec b) = Real.sqrt (∑ i : Fin d, ‖b i‖ ^ 2) := by
  rw [l2norm, sum_sq_sectorVec]

theorem l2norm_sectorVec_sq (b : Fin d → ℂ) :
    l2norm (sectorVec b) ^ 2 = ∑ i : Fin d, ‖b i‖ ^ 2 := by
  rw [l2norm_sectorVec, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]

/-- **Module 3's bound in the `Fin d` sector.**  For every coupling `b` on the `d` modes and every
`t > 0`,

`|Re⟪u, Σᵢ(bᵢ/√2)(aᵢ† − aᵢ)u⟫| ≤ t⟪u, N u⟫ + (∑ᵢ‖bᵢ‖²/t)‖u‖²`,

which is `driftField_relative_form_bound` with the `ℓ²` norm of the coupling written in the
chapter's own indexing: `d` is the number of modes, the coupling is a `Fin d` family, and the
constant is the coefficient norm rather than a `ℕ`-supported `Finsupp`. -/
theorem driftField_sector_relative_form_bound (b : Fin d → ℂ) {t : ℝ} (ht : 0 < t)
    (u : FockAlg) :
    |(inner ℂ (toLp u) (toLp (driftField (sectorVec b) u)) : ℂ).re|
      ≤ t * numberQuad u + (∑ i : Fin d, ‖b i‖ ^ 2) / t * ‖toLp u‖ ^ 2 := by
  have h := driftField_relative_form_bound (sectorVec b) ht u
  rw [l2norm_sectorVec_sq] at h
  exact h

/-! ### The sector of the Fock model -/

/-- A Fock state **lives in the `Fin d` mode sector** when every mode any of its configurations
excites is one of the first `d`. -/
def InSector (d : ℕ) (u : FockAlg) : Prop := modes u ⊆ Finset.range d

theorem support_sub_subset (u v : FockAlg) :
    (u - v).support ⊆ u.support ∪ v.support := by
  intro β hβ
  rw [Finset.mem_union]
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  exact (Finsupp.mem_support_iff.mp hβ) (by
    rw [Finsupp.sub_apply, Finsupp.notMem_support_iff.mp h1, Finsupp.notMem_support_iff.mp h2,
      sub_zero])

theorem modes_add_subset (u v : FockAlg) : modes (u + v) ⊆ modes u ∪ modes v := by
  intro k hk
  obtain ⟨β, hβ, hkβ⟩ := Finset.mem_biUnion.mp hk
  rcases Finset.mem_union.mp (Finsupp.support_add hβ) with h | h
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨β, h, hkβ⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨β, h, hkβ⟩)

theorem modes_sub_subset (u v : FockAlg) : modes (u - v) ⊆ modes u ∪ modes v := by
  intro k hk
  obtain ⟨β, hβ, hkβ⟩ := Finset.mem_biUnion.mp hk
  rcases Finset.mem_union.mp (support_sub_subset u v hβ) with h | h
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨β, h, hkβ⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨β, h, hkβ⟩)

theorem modes_smul_subset (c : ℂ) (u : FockAlg) : modes (c • u) ⊆ modes u := by
  intro k hk
  obtain ⟨β, hβ, hkβ⟩ := Finset.mem_biUnion.mp hk
  exact Finset.mem_biUnion.mpr ⟨β, Finsupp.support_smul hβ, hkβ⟩

theorem modes_annA_subset (j : ℕ) (u : FockAlg) : modes (annA j u) ⊆ modes u := by
  intro k hk
  obtain ⟨β, hβ, hkβ⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp (support_annA j u hβ)
  exact Finset.mem_biUnion.mpr ⟨α, hα, support_dn j α hkβ⟩

theorem modes_creA_subset (j : ℕ) (u : FockAlg) : modes (creA j u) ⊆ insert j (modes u) := by
  intro k hk
  obtain ⟨β, hβ, hkβ⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp (support_creA j u hβ)
  rcases Finset.mem_insert.mp (support_up j α hkβ) with h | h
  · exact Finset.mem_insert.mpr (Or.inl h)
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨α, hα, h⟩))

theorem modes_sum_subset {ι : Type*} (s : Finset ι) (g : ι → FockAlg) :
    modes (∑ i ∈ s, g i) ⊆ s.biUnion (fun i => modes (g i)) := by
  classical
  induction s using Finset.induction with
  | empty => simp [modes]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.biUnion_insert]
    exact (modes_add_subset _ _).trans
      (Finset.union_subset_union (Finset.Subset.refl _) ih)

theorem modes_annVec_subset (f : ℕ →₀ ℂ) (u : FockAlg) : modes (annVec f u) ⊆ modes u := by
  rw [annVec_apply]
  refine (modes_sum_subset f.support (fun j => ((starRingEnd ℂ) (f j)) • annA j u)).trans ?_
  intro k hk
  obtain ⟨j, _, hkj⟩ := Finset.mem_biUnion.mp hk
  exact (modes_smul_subset _ _).trans (modes_annA_subset j u) hkj

theorem modes_creVec_subset (f : ℕ →₀ ℂ) (u : FockAlg) :
    modes (creVec f u) ⊆ f.support ∪ modes u := by
  rw [creVec_apply]
  refine (modes_sum_subset f.support (fun j => (f j) • creA j u)).trans ?_
  intro k hk
  obtain ⟨j, hj, hkj⟩ := Finset.mem_biUnion.mp hk
  have h1 : k ∈ modes (creA j u) := (modes_smul_subset (f j) (creA j u)) hkj
  rcases Finset.mem_insert.mp (modes_creA_subset j u h1) with h | h
  · exact Finset.mem_union_left _ (h ▸ hj)
  · exact Finset.mem_union_right _ h

/-- **The drift cannot leave the `Fin d` mode sector.**  Annihilation does not change the modes
at all, and creation only adds modes drawn from the coupling's support, so a coupling supported
on the first `d` modes maps the sector into itself. -/
theorem modes_driftField_subset (f : ℕ →₀ ℂ) (u : FockAlg) :
    modes (driftField f u) ⊆ f.support ∪ modes u := by
  rw [driftField_apply]
  refine (modes_sub_subset (creVec f u) (annVec f u)).trans ?_
  refine Finset.union_subset (modes_creVec_subset f u) ?_
  exact (modes_annVec_subset f u).trans Finset.subset_union_right

theorem InSector.driftField (b : Fin d → ℂ) {u : FockAlg} (h : InSector d u) :
    InSector d (driftField (sectorVec b) u) :=
  (modes_driftField_subset (sectorVec b) u).trans
    (Finset.union_subset (support_sectorVec b) h)

/-- In the sector, every mode beyond `d` is annihilated: `a_k = 0` on the sector for `k ≥ d`. -/
theorem annA_eq_zero_of_sector {u : FockAlg} (h : InSector d u) {k : ℕ} (hk : d ≤ k) :
    annA k u = 0 := by
  refine annA_eq_zero_of_not_mem_modes (fun hmem => ?_)
  have hm := h hmem
  rw [Finset.mem_range] at hm
  omega

/-- **The number form reindexed onto `Fin d`.**  On the sector, `⟪u, N u⟫` is the sum of the
`d` mode contributions `‖aᵢ u‖²` — the corpus form of §5's `numberForm`. -/
theorem numberQuad_eq_sum_fin {u : FockAlg} (h : InSector d u) :
    numberQuad u = ∑ i : Fin d, ‖toLp (annA (i : ℕ) u)‖ ^ 2 := by
  rw [numberQuad_eq_sum (K := Finset.range d) h]
  exact Finset.sum_range (fun j => ‖toLp (annA j u)‖ ^ 2)

end Sector

/-! ## 9. The Hermite expansion of the gradient: the multiplication law `x_j = (a_j + a_j†)/√2`

The module's honest boundary recorded the Hermite expansion of `∇Φ` as the missing input of
Module 3.  Half of it is the multiplication law, and that half is here: `x_j` on the core is the
two-letter ladder word `(a_j† + a_j)/√2`, with the *same* Hermite amplitudes `√(n_j + 1)` and
`√(n_j)` the drift uses.  Together with `driftOpCoeff` (the gradient `∂_j = (a_j − a_j†)/√2`),
this is the dictionary that turns a polynomial in `(x, ∂)` into a finite family of ladder words:
every `x_j` and every `∂_j` is a word of length one, and a monomial of degree `k` becomes a word
of length `≤ k`. -/

/-- **The Hermite multiplication `x_j = (a_j + a_j†)/√2` on the core**: two ladder words of length
one with the Hermite normalization `1/√2`.  This is the `x_j = (a_j + a_j†)/√2` half of the
expansion, the mirror image of `driftOpCoeff`'s `∂_j = (a_j − a_j†)/√2`. -/
def mulHermite (j : Fin d) (c : CoreCoeff d) : CoreCoeff d :=
  (invSqrtTwo : ℂ) • (hopStep (j, true) c + hopStep (j, false) c)

/-- A ladder letter sends the zero family to zero. -/
theorem hopStep_zero (p : Fin d × Bool) : hopStep p (0 : CoreCoeff d) = 0 := by
  unfold hopStep
  simp

/-- **A ladder letter is additive** on the core: linearity in the coefficient family, the first
half of the linearity the expansion needs. -/
theorem hopStep_add (p : Fin d × Bool) (x y : CoreCoeff d) :
    hopStep p (x + y) = hopStep p x + hopStep p y := by
  unfold hopStep
  exact Finsupp.sum_add_index' (fun a => by simp) (fun a b₁ b₂ => by simp [mul_add])

/-- A ladder letter commutes with finite sums. -/
theorem hopStep_sum {ι : Type*} (p : Fin d × Bool) (s : Finset ι) (g : ι → CoreCoeff d) :
    hopStep p (∑ i ∈ s, g i) = ∑ i ∈ s, hopStep p (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [hopStep_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hopStep_add, ih]

/-- **Words concatenate**: applying `w₁` and then `w₂` is applying the concatenated word. -/
theorem hopWord_append : ∀ (w₁ w₂ : List (Fin d × Bool)) (c : CoreCoeff d),
    hopWord (w₁ ++ w₂) c = hopWord w₂ (hopWord w₁ c) := by
  intro w₁
  induction w₁ with
  | nil => intro w₂ c; rfl
  | cons p w ih =>
    intro w₂ c
    change hopWord (w ++ w₂) (hopStep p c) = hopWord w₂ (hopWord w (hopStep p c))
    exact ih w₂ (hopStep p c)

/-- A two-letter word, spelled out: the letters are applied right to left. -/
theorem hopWord_two (p q : Fin d × Bool) (c : CoreCoeff d) :
    hopWord [p, q] c = hopStep q (hopStep p c) := rfl

/-- A one-letter word is a single letter. -/
theorem hopWord_single (p : Fin d × Bool) (c : CoreCoeff d) :
    hopWord [p] c = hopStep p c := rfl

/-- **A ladder letter is `ℂ`-linear** on the core (scalar half). -/
theorem hopStep_smul (p : Fin d × Bool) (r : ℂ) (x : CoreCoeff d) :
    hopStep p (r • x) = r • hopStep p x := by
  unfold hopStep
  rw [Finsupp.sum_smul_index' (fun i => by simp)]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_left_comm, Finsupp.sum, Finset.smul_sum]

/-- The multiplication law is additive on the core. -/
theorem mulHermite_add (j : Fin d) (x y : CoreCoeff d) :
    mulHermite j (x + y) = mulHermite j x + mulHermite j y := by
  simp only [mulHermite, hopStep_add, smul_add]
  abel

/-- The multiplication law is `ℂ`-linear on the core. -/
theorem mulHermite_smul (j : Fin d) (r : ℂ) (c : CoreCoeff d) :
    mulHermite j (r • c) = r • mulHermite j c := by
  rw [mulHermite, mulHermite, hopStep_smul, hopStep_smul, smul_add, smul_add, smul_smul,
    smul_smul, mul_comm (invSqrtTwo : ℂ) r, smul_add, smul_smul, smul_smul]

/-- **The two-mode product law**: multiplying twice is `1/2` times the sum of the four length-two
ladder words.  This is the first nontrivial case of the multimode expansion — the `2^2` word
family with the amplitudes carried by the `hopStep`s. -/
theorem mulHermite_comp (j k : Fin d) (c : CoreCoeff d) :
    mulHermite k (mulHermite j c)
      = ((invSqrtTwo : ℂ) * invSqrtTwo) •
          (hopWord [(j, true), (k, true)] c + hopWord [(j, true), (k, false)] c
            + hopWord [(j, false), (k, true)] c + hopWord [(j, false), (k, false)] c) := by
  rw [mulHermite, mulHermite, hopStep_smul, hopStep_smul, hopStep_add, hopStep_add]
  rw [← smul_add, ← smul_smul]
  congr 1
  rw [← hopWord_two, ← hopWord_two, ← hopWord_two, ← hopWord_two]
  abel

/-- **The multiplication law, written as the sum of its two ladder words** — the form the
expansion consumes, with the coefficient `1/√2` pushed onto each letter. -/
theorem mulHermite_eq_ladderWords (j : Fin d) (c : CoreCoeff d) :
    mulHermite j c
      = ((invSqrtTwo : ℝ) : ℂ) • hopStep (j, true) c
        + ((invSqrtTwo : ℝ) : ℂ) • hopStep (j, false) c := by
  simp only [mulHermite, smul_add]

/-- **The gradient's ladder words**, symmetrically: `K_drift = −Σ_j b_j ∂_j` is the two-letter
family `−b_j/√2 · a_j` and `+b_j/√2 · a_j†`, separated into the lowering and raising sums. -/
theorem driftOpCoeff_eq_ladderWords (b : Fin d → ℝ) (c : CoreCoeff d) :
    driftOpCoeff b c
      = ∑ j : Fin d, (((-(b j)) * invSqrtTwo : ℝ) : ℂ) • hopStep (j, false) c
        + ∑ j : Fin d, (((b j) * invSqrtTwo : ℝ) : ℂ) • hopStep (j, true) c :=
  Finset.sum_add_distrib

/-- **The dictionary is complete for linear potentials.**  If `Φ(u) = Σ_j c_j u_j` then
`∂_j Φ = c_j`, so the drift coefficient is `b_j = (β²σ²/2)·c_j` and `K_drift` is the ladder-word
family of `driftOpCoeff`.  This is the case of the Hermite expansion in which `∇Φ` is constant,
proved for every mode family `b`; the polynomial case needs the induction over `MvPolynomial`
that composes `mulHermite` (the words of `x`) with `driftOpCoeff` (the words of `∂`), which the
corpus does not yet have. -/
-- the coefficients of a linear potential's gradient need no further identity: `b` *is* `∇Φ` up
-- to the constant `β²σ²/2`, and `driftOpCoeff` is by definition the ladder-word expansion of it.
example (b : Fin d → ℝ) (c : CoreCoeff d) :
    driftOpCoeff b c
      = ∑ j : Fin d, (((-(b j)) * invSqrtTwo : ℝ) : ℂ) • hopStep (j, false) c
        + ∑ j : Fin d, (((b j) * invSqrtTwo : ℝ) : ℂ) • hopStep (j, true) c :=
  driftOpCoeff_eq_ladderWords b c

end BookProof.MCMC.FockLangevin
