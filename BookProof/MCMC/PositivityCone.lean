import BookProof.MCMC.FockLangevinOperator

/-!
# Chapter PositivityCone — the pCNL step on the positivity cone, and its invariant state

`pcnl.md`'s Module 4–5 asks for the pCNL chain's convergence to its invariant measure.  The core
`ℓ²` model of `BookProof/MCMC/FockLangevinOperator` cannot answer it: §19 records the reason and
§20–§21 sharpen it — on the core the normalisation `P 1 = 1` holds (§20) but the drift's pairing
with the *flat* `ℓ¹` measure is positive at every basis vector (§21), so the strict contraction a
convergence argument needs is not a statement about that pairing.  This module supplies the model
in which the question is answered: the step as a **transition kernel on the positive cone**.

## The model

`step Q f = Q · f` with `Q : Fin (m+1) → Fin (m+1) → ℝ` a **row-stochastic** kernel — `P 1 = 1`
(`step_one`) — that is also **column-stochastic** (`ColStoch`, so the `ℓ¹` mass is preserved:
`mass_step`), **positive** (`step_nonneg` preserves `Cone`) and **uniformly positive**: a Doeblin
minorant `δ > 0` on every entry.  The uniform minorant is what the pCNL proposal supplies — its
Gaussian increment has a positive density everywhere — and it is exactly the hypothesis a
Dobrushin/Doeblin argument consumes.

## What is proved

* **`P 1 = 1`** — `step_one`, and `step_const` in the concrete instance;
* **the cone and the mass** — `step_nonneg` (positivity is preserved) and `mass_step`, `mass_iter`
  (the `ℓ¹` mass of the density is invariant);
* **the Doeblin contraction** — `sum_abs_row_diff_le` (`∑ₖ |Q a k − Q b k| ≤ 2(1 − (m+1)δ)` from the
  minorant) and `abs_step_sub_step_le`, giving the oscillation contraction
  **`osc_step_le`: `osc (P f) ≤ (1 − (m+1)δ)·osc f`**, and its iterate form `osc_iter_le`;
* **convergence to the invariant state** — **`tendsto_iter_step`**: for every starting density and
  every state, the iterates converge to the single limit `mass f / (m+1)`, geometrically at rate
  `1 − (m+1)δ`.  The limit is the uniform density — the invariant state of a doubly stochastic
  kernel — and it does not depend on the start;
* **the concrete pCNL kernel** — `uniformStep t` (hold with the Metropolis mass, jump with proposal
  mass `t`), with `uniformStep_rowStoch`, `uniformStep_colStoch`, `uniformStep_pos`,
  `uniformStep_cone`, **`uniformStep_one`** and the instance of the convergence theorem
  **`tendsto_iter_uniformStep`**;
* **the prescribed target (§23)** — the pCNL invariant measure is not flat, so the section replaces
  column stochasticity by a target `π` with a Doeblin condition `ε π b ≤ Q a b`
  (`Target`, `Minorant`, `Stationary`): `sum_abs_sub_minorant` gives `∑_b |Q a b − ε π b| = 1 − ε`,
  `l1_apply_le` the one-step `ℓ¹` contraction, and **`tendsto_iter_target`** proves
  `‖f Qⁿ − π‖₁ ≤ (1 − ε)ⁿ ‖f − π‖₁ → 0`.  The concrete kernel `targetKernel ε π` (hold with
  `1 − ε`, else draw from `π`) satisfies all hypotheses (`targetKernel_rowStoch`,
  `targetKernel_minorant`, `targetKernel_stationary`) and instantiates the theorem
  (`tendsto_iter_targetKernel`, `tendsto_iter_targetKernel_apply`); `uniformStep_eq_targetKernel`
  identifies §22's kernel as the flat-target special case.

## Where the `ℓ²` core and this model meet

The last section states the Module 4–5 hypotheses of
`BookProof.MCMC.UnadjustedPCN.pcn_geometric_ergodicity` — invariant state, sector contraction, gap
`1 − ρ > 0` — discharged by §18's facts (`module45_hypotheses_cited`), so the pCNL gap hypothesis
cites the operator module instead of assuming it.
-/

namespace BookProof.MCMC.PositivityCone

open Finset Filter
open scoped Topology

variable {m : ℕ}

/-! ## The cone and the step -/

/-- The positive cone: nonnegative densities on the finite occupation space. -/
def Cone (f : Fin (m + 1) → ℝ) : Prop := ∀ a, 0 ≤ f a

/-- The pCNL step read as a transition kernel: `(P f) a = ∑ₖ Q a k f k`. -/
def step (Q : Fin (m + 1) → Fin (m + 1) → ℝ) (f : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  fun a => ∑ k, Q a k * f k

/-- The `ℓ¹` mass of a density. -/
def mass (f : Fin (m + 1) → ℝ) : ℝ := ∑ a, f a

/-- Row stochasticity: `P 1 = 1`. -/
def RowStoch (Q : Fin (m + 1) → Fin (m + 1) → ℝ) : Prop := ∀ a, ∑ k, Q a k = 1

/-- Column stochasticity: the step preserves the `ℓ¹` mass (the pCN proposal is symmetric). -/
def ColStoch (Q : Fin (m + 1) → Fin (m + 1) → ℝ) : Prop := ∀ k, ∑ a, Q a k = 1

/-- Uniform positivity (the pCN Gaussian proposal has a positive density everywhere): a Doeblin
minorant `δ > 0` for the transition kernel. -/
def UniformPos (Q : Fin (m + 1) → Fin (m + 1) → ℝ) (δ : ℝ) : Prop := ∀ a k, δ ≤ Q a k

/-- The maximum of a vector, as a finite supremum. -/
def supv (f : Fin (m + 1) → ℝ) : ℝ := univ.sup' ⟨0, mem_univ 0⟩ f

/-- The oscillation `max f + max (−f) = max f − min f`: the diameter of the range. -/
def osc (f : Fin (m + 1) → ℝ) : ℝ := supv f + supv (fun a => -f a)

theorem sum_const' (c : ℝ) : (∑ _a : Fin (m + 1), c) = ((m : ℝ) + 1) * c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem le_supv (f : Fin (m + 1) → ℝ) (a : Fin (m + 1)) : f a ≤ supv f :=
  Finset.le_sup' f (mem_univ a)

theorem neg_le_supv (f : Fin (m + 1) → ℝ) (a : Fin (m + 1)) : -f a ≤ supv (fun k => -f k) :=
  Finset.le_sup' (fun k => -f k) (mem_univ a)

theorem osc_nonneg (f : Fin (m + 1) → ℝ) : 0 ≤ osc f := by
  have h1 := le_supv f 0
  have h2 := neg_le_supv f 0
  simp only [osc, supv] at *
  linarith

theorem abs_sub_le_osc (f : Fin (m + 1) → ℝ) (a b : Fin (m + 1)) : |f a - f b| ≤ osc f := by
  have h1 := le_supv f a
  have h2 := neg_le_supv f a
  have h3 := le_supv f b
  have h4 := neg_le_supv f b
  simp only [osc, supv] at *
  refine abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_sub_center_le_osc (f : Fin (m + 1) → ℝ) (a : Fin (m + 1)) :
    |f a - (supv f - supv (fun k => -f k)) / 2| ≤ osc f / 2 := by
  have h1 := le_supv f a
  have h2 := neg_le_supv f a
  simp only [osc, supv] at *
  refine abs_le.mpr ⟨by linarith, by linarith⟩

/-! ### The step, on the cone -/

theorem step_one {Q : Fin (m + 1) → Fin (m + 1) → ℝ} (hQ : RowStoch Q) :
    step Q (fun _ => (1 : ℝ)) = fun _ => 1 := by
  funext a
  simp [step, hQ a]

theorem step_nonneg {Q : Fin (m + 1) → Fin (m + 1) → ℝ} (hQ : ∀ a k, 0 ≤ Q a k)
    {f : Fin (m + 1) → ℝ} (hf : Cone f) : Cone (step Q f) :=
  fun a => Finset.sum_nonneg fun k _ => mul_nonneg (hQ a k) (hf k)

theorem mass_step {Q : Fin (m + 1) → Fin (m + 1) → ℝ} (hQ : ColStoch Q)
    (f : Fin (m + 1) → ℝ) : mass (step Q f) = mass f := by
  simp only [mass, step]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_mul, hQ k, one_mul]

theorem mass_iter {Q : Fin (m + 1) → Fin (m + 1) → ℝ} (hQ : ColStoch Q)
    (f : Fin (m + 1) → ℝ) (n : ℕ) : mass ((step Q)^[n] f) = mass f := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', mass_step hQ, ih]

/-! ### The Dobrushin estimate -/

theorem step_sub_step (Q : Fin (m + 1) → Fin (m + 1) → ℝ) (f : Fin (m + 1) → ℝ)
    (a b : Fin (m + 1)) :
    step Q f a - step Q f b = ∑ k, (Q a k - Q b k) * f k := by
  simp only [step]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => (sub_mul _ _ _).symm

theorem sum_row_diff {Q : Fin (m + 1) → Fin (m + 1) → ℝ} (hQ : RowStoch Q)
    (a b : Fin (m + 1)) : ∑ k, (Q a k - Q b k) = 0 := by
  rw [Finset.sum_sub_distrib, hQ a, hQ b, sub_self]

theorem step_sub_step_centered {Q : Fin (m + 1) → Fin (m + 1) → ℝ} (hQ : RowStoch Q)
    (f : Fin (m + 1) → ℝ) (c : ℝ) (a b : Fin (m + 1)) :
    step Q f a - step Q f b = ∑ k, (Q a k - Q b k) * (f k - c) := by
  have hzero : ∑ k, (Q a k - Q b k) * c = 0 := by
    rw [← Finset.sum_mul, sum_row_diff hQ, zero_mul]
  rw [step_sub_step]
  calc ∑ k, (Q a k - Q b k) * f k
      = ∑ k, ((Q a k - Q b k) * (f k - c) + (Q a k - Q b k) * c) :=
        Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ k, (Q a k - Q b k) * (f k - c) + ∑ k, (Q a k - Q b k) * c :=
        Finset.sum_add_distrib
    _ = ∑ k, (Q a k - Q b k) * (f k - c) := by rw [hzero, add_zero]

theorem sum_abs_row_diff_le {Q : Fin (m + 1) → Fin (m + 1) → ℝ} (hQ : RowStoch Q) {δ : ℝ}
    (hδ : UniformPos Q δ) (a b : Fin (m + 1)) :
    ∑ k, |Q a k - Q b k| ≤ 2 * (1 - ((m : ℝ) + 1) * δ) := by
  have hpt : ∀ k, |Q a k - Q b k| ≤ (Q a k - Q b k) + 2 * (Q b k - δ) := by
    intro k
    have ha := hδ a k
    have hb := hδ b k
    refine abs_le.mpr ⟨by linarith, by linarith⟩
  calc ∑ k, |Q a k - Q b k|
      ≤ ∑ k, ((Q a k - Q b k) + 2 * (Q b k - δ)) := Finset.sum_le_sum fun k _ => hpt k
    _ = 2 * (1 - ((m : ℝ) + 1) * δ) := by
        have hsum1 : ∑ k, (Q a k - Q b k) = 0 := sum_row_diff hQ a b
        have hsum2 : ∑ k, (Q b k - δ) = 1 - ((m : ℝ) + 1) * δ := by
          rw [Finset.sum_sub_distrib, hQ b, sum_const']
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum1, hsum2]
        ring

theorem abs_step_sub_step_le {Q : Fin (m + 1) → Fin (m + 1) → ℝ} (hQ : RowStoch Q) {δ : ℝ}
    (hδ : UniformPos Q δ) (f : Fin (m + 1) → ℝ) (a b : Fin (m + 1)) :
    |step Q f a - step Q f b| ≤ (1 - ((m : ℝ) + 1) * δ) * osc f := by
  set c := (supv f - supv (fun k => -f k)) / 2 with hc
  have hg : ∀ k, |f k - c| ≤ osc f / 2 := fun k => abs_sub_center_le_osc f k
  calc |step Q f a - step Q f b|
      = |∑ k, (Q a k - Q b k) * (f k - c)| := by rw [step_sub_step_centered hQ f c a b]
    _ ≤ ∑ k, |(Q a k - Q b k) * (f k - c)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |Q a k - Q b k| * |f k - c| := by simp only [abs_mul]
    _ ≤ ∑ k, |Q a k - Q b k| * (osc f / 2) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hg k) (abs_nonneg _)
    _ = (∑ k, |Q a k - Q b k|) * (osc f / 2) := by rw [Finset.sum_mul]
    _ ≤ (2 * (1 - ((m : ℝ) + 1) * δ)) * (osc f / 2) :=
        mul_le_mul_of_nonneg_right (sum_abs_row_diff_le hQ hδ a b)
          (div_nonneg (osc_nonneg f) (by norm_num))
    _ = (1 - ((m : ℝ) + 1) * δ) * osc f := by ring

theorem osc_step_le {Q : Fin (m + 1) → Fin (m + 1) → ℝ} (hQ : RowStoch Q) {δ : ℝ}
    (hδ : UniformPos Q δ) (f : Fin (m + 1) → ℝ) :
    osc (step Q f) ≤ (1 - ((m : ℝ) + 1) * δ) * osc f := by
  have hpoint : ∀ a b, |step Q f a - step Q f b| ≤ (1 - ((m : ℝ) + 1) * δ) * osc f :=
    abs_step_sub_step_le hQ hδ f
  have hT : ∀ a, supv (fun x => -step Q f x) ≤ -step Q f a + (1 - ((m : ℝ) + 1) * δ) * osc f := by
    intro a
    refine Finset.sup'_le ⟨0, mem_univ 0⟩ _ fun b _ => ?_
    have h := (abs_le.mp (hpoint a b)).2
    linarith
  have hsup : supv (step Q f) ≤ (1 - ((m : ℝ) + 1) * δ) * osc f
      - supv (fun x => -step Q f x) := by
    refine Finset.sup'_le ⟨0, mem_univ 0⟩ _ fun a _ => ?_
    have h := hT a
    linarith
  simp only [osc, supv] at *
  linarith

theorem osc_iter_le {Q : Fin (m + 1) → Fin (m + 1) → ℝ} (hQ : RowStoch Q) {δ : ℝ}
    (hδ : UniformPos Q δ) (f : Fin (m + 1) → ℝ) (n : ℕ) :
    osc ((step Q)^[n] f) ≤ (1 - ((m : ℝ) + 1) * δ) ^ n * osc f := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcard : ((m : ℝ) + 1) * δ ≤ 1 := by
      calc ((m : ℝ) + 1) * δ = ∑ _k : Fin (m + 1), δ := (sum_const' δ).symm
        _ ≤ ∑ k : Fin (m + 1), Q 0 k := Finset.sum_le_sum fun k _ => hδ 0 k
        _ = 1 := hQ 0
    have hnonneg : (0 : ℝ) ≤ 1 - ((m : ℝ) + 1) * δ := by linarith
    rw [Function.iterate_succ_apply', pow_succ]
    calc osc (step Q ((step Q)^[n] f))
        ≤ (1 - ((m : ℝ) + 1) * δ) * osc ((step Q)^[n] f) := osc_step_le hQ hδ _
      _ ≤ (1 - ((m : ℝ) + 1) * δ) * ((1 - ((m : ℝ) + 1) * δ) ^ n * osc f) :=
          mul_le_mul_of_nonneg_left ih hnonneg
      _ = (1 - ((m : ℝ) + 1) * δ) ^ n * (1 - ((m : ℝ) + 1) * δ) * osc f := by ring

/-! ### Convergence to the invariant state -/

theorem tendsto_iter_step {Q : Fin (m + 1) → Fin (m + 1) → ℝ} (hQ : RowStoch Q)
    (hQc : ColStoch Q) {δ : ℝ} (hδ0 : 0 < δ) (hδ : UniformPos Q δ)
    (f : Fin (m + 1) → ℝ) (a : Fin (m + 1)) :
    Tendsto (fun n => ((step Q)^[n] f) a) atTop (𝓝 (mass f / ((m : ℝ) + 1))) := by
  set lam := 1 - ((m : ℝ) + 1) * δ with hlam
  have hcard : ((m : ℝ) + 1) * δ ≤ 1 := by
    calc ((m : ℝ) + 1) * δ = ∑ _k : Fin (m + 1), δ := (sum_const' δ).symm
      _ ≤ ∑ k : Fin (m + 1), Q 0 k := Finset.sum_le_sum fun k _ => hδ 0 k
      _ = 1 := hQ 0
  have hlam_one : lam < 1 := by
    have : 0 < ((m : ℝ) + 1) * δ := by positivity
    simp only [hlam]
    linarith
  have hlam_nonneg : 0 ≤ lam := by
    simp only [hlam]
    linarith
  have hpow : Tendsto (fun n => lam ^ n * osc f) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam_nonneg hlam_one).mul_const (osc f)
  have hbound : ∀ n, |((step Q)^[n] f) a - mass f / ((m : ℝ) + 1)| ≤ lam ^ n * osc f := by
    intro n
    set g := (step Q)^[n] f with hg
    have hmass : mass g = mass f := mass_iter hQc f n
    have hcardpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hright : ∑ k, (g a - g k) = ((m : ℝ) + 1) * g a - mass g := by
      rw [Finset.sum_sub_distrib, sum_const' (g a)]
      rfl
    have hkey : ((m : ℝ) + 1) * (g a - mass f / ((m : ℝ) + 1)) = ∑ k, (g a - g k) := by
      rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hcardpos), hright, hmass]
    have hsum : |∑ k, (g a - g k)| ≤ ((m : ℝ) + 1) * osc g := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k, |g a - g k| ≤ ∑ _k : Fin (m + 1), osc g :=
            Finset.sum_le_sum fun k _ => abs_sub_le_osc g a k
        _ = ((m : ℝ) + 1) * osc g := sum_const' (osc g)
    have hosc := osc_iter_le hQ hδ f n
    rw [← hg] at hosc
    have hmul : ((m : ℝ) + 1) * |g a - mass f / ((m : ℝ) + 1)|
        ≤ ((m : ℝ) + 1) * osc g := by
      nth_rewrite 1 [← abs_of_pos hcardpos]
      rw [← abs_mul, hkey]
      exact hsum
    exact (le_of_mul_le_mul_left hmul hcardpos).trans hosc
  have habs : Tendsto (fun n => |((step Q)^[n] f) a - mass f / ((m : ℝ) + 1)|) atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _) hbound hpow
  have hz : Tendsto (fun n => ((step Q)^[n] f) a - mass f / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using habs
  have := hz.add_const (mass f / ((m : ℝ) + 1))
  simpa [sub_add_cancel] using this

/-! ### The concrete uniformly positive pCN kernel -/

/-- The pCNL kernel of a symmetric proposal: hold at `a` with the Metropolis mass, jump to any other
state with the proposal mass `t`.  Every entry is at least `t` — the Doeblin minorant of the
Gaussian proposal's positive density. -/
def uniformStep (t : ℝ) : Fin (m + 1) → Fin (m + 1) → ℝ :=
  fun a k => t + if k = a then 1 - ((m : ℝ) + 1) * t else 0

theorem uniformStep_rowStoch (m : ℕ) (t : ℝ) : RowStoch (uniformStep (m := m) t) := by
  intro a
  have h1 : (∑ k : Fin (m + 1),
      (if k = a then 1 - ((m : ℝ) + 1) * t else (0 : ℝ))) = 1 - ((m : ℝ) + 1) * t := by
    rw [Finset.sum_ite_eq']
    simp
  calc ∑ k : Fin (m + 1), uniformStep t a k
      = ∑ k : Fin (m + 1),
          (t + if k = a then 1 - ((m : ℝ) + 1) * t else (0 : ℝ)) := rfl
    _ = (∑ _k : Fin (m + 1), t)
          + ∑ k : Fin (m + 1),
            (if k = a then 1 - ((m : ℝ) + 1) * t else (0 : ℝ)) := Finset.sum_add_distrib
    _ = ((m : ℝ) + 1) * t + (1 - ((m : ℝ) + 1) * t) := by rw [sum_const', h1]
    _ = 1 := by ring

theorem uniformStep_colStoch (m : ℕ) (t : ℝ) : ColStoch (uniformStep (m := m) t) := by
  intro k
  have h1 : (∑ a : Fin (m + 1),
      (if k = a then 1 - ((m : ℝ) + 1) * t else (0 : ℝ))) = 1 - ((m : ℝ) + 1) * t := by
    rw [Finset.sum_ite_eq]
    simp
  calc ∑ a : Fin (m + 1), uniformStep t a k
      = ∑ a : Fin (m + 1),
          (t + if k = a then 1 - ((m : ℝ) + 1) * t else (0 : ℝ)) := rfl
    _ = (∑ _a : Fin (m + 1), t)
          + ∑ a : Fin (m + 1),
            (if k = a then 1 - ((m : ℝ) + 1) * t else (0 : ℝ)) := Finset.sum_add_distrib
    _ = ((m : ℝ) + 1) * t + (1 - ((m : ℝ) + 1) * t) := by rw [sum_const', h1]
    _ = 1 := by ring

theorem uniformStep_pos (m : ℕ) {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : ((m : ℝ) + 1) * t ≤ 1) :
    UniformPos (uniformStep (m := m) t) t := by
  intro a k
  simp only [uniformStep]
  split_ifs with h
  · linarith
  · linarith

theorem uniformStep_nonneg (m : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : ((m : ℝ) + 1) * t ≤ 1) :
    ∀ a k, 0 ≤ uniformStep (m := m) t a k := by
  intro a k
  simp only [uniformStep]
  split_ifs with h
  · linarith
  · linarith

/-- The step preserves the positive cone. -/
theorem uniformStep_cone (m : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : ((m : ℝ) + 1) * t ≤ 1)
    {f : Fin (m + 1) → ℝ} (hf : Cone f) : Cone (step (uniformStep (m := m) t) f) :=
  step_nonneg (uniformStep_nonneg m ht0 ht1) hf

/-- **The pCNL step on the positivity cone: `P 1 = 1`.** -/
theorem uniformStep_one (m : ℕ) (t : ℝ) :
    step (uniformStep (m := m) t) (fun _ => (1 : ℝ)) = fun _ => 1 :=
  step_one (uniformStep_rowStoch m t)

/-- **The cone model's convergence theorem.**  For the uniformly positive pCNL kernel, the iterates
of any density converge to the invariant state `1` at the geometric rate `1 − (m+1)t`. -/
theorem tendsto_iter_uniformStep (m : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : ((m : ℝ) + 1) * t ≤ 1)
    (f : Fin (m + 1) → ℝ) (a : Fin (m + 1)) :
    Tendsto (fun n => ((step (uniformStep (m := m) t))^[n] f) a) atTop
      (𝓝 (mass f / ((m : ℝ) + 1))) :=
  tendsto_iter_step (uniformStep_rowStoch m t) (uniformStep_colStoch m t) ht0
    (uniformStep_pos m ht0.le ht1) f a

/-! ## 23. The prescribed target: convergence to `π`, not to the flat density

§22's conclusion is uniform because its kernel is doubly stochastic.  The pCNL chain's invariant
measure is not flat, so this section replaces the column-stochastic hypothesis by three facts about
a **prescribed target** `π`:

* `Target π` — `π ≥ 0` and `∑ π = 1`;
* `Minorant Q π ε` — the Doeblin condition `ε · π b ≤ Q a b` *relative to* `π` (what a Metropolis
  kernel with proposal `π` and acceptance bounded below by `ε` supplies);
* `Stationary Q π` — `∑ₐ π a Q a b = π b`.

The `ℓ¹` step is the same computation as §22 with `π` in place of the uniform density: on a signed
measure of zero total mass the constant part of the minorant cancels (`apply_eq_sum_sub`), so
`∑_b |Q a b − ε π b| = 1 − ε` (`sum_abs_sub_minorant`) and one step scales the `ℓ¹` mass by at most
`1 − ε` (`l1_apply_le`, iterated in `l1_apply_iter_le`).  Stationarity turns that into convergence
of the *iterates* to `π` — **`tendsto_iter_target`**: `‖f Qⁿ − π‖₁ ≤ (1 − ε)ⁿ ‖f − π‖₁ → 0` for
every starting probability vector — and `tendsto_iter_target_pointwise` reads it coordinatewise.

`targetKernel ε π` is the concrete kernel: hold with mass `1 − ε`, otherwise draw from `π`.  It is
row stochastic (`targetKernel_rowStoch`), has minorant `ε` (`targetKernel_minorant`), is stationary
at `π` (`targetKernel_stationary`), and **`tendsto_iter_targetKernel`** is the convergence theorem
for it (`tendsto_iter_targetKernel_apply` coordinatewise).  `uniformStep_eq_targetKernel` shows
§22's kernel is the special case of a flat target, so the two models are one. -/

/-- The `ℓ¹` norm of a signed measure. -/
def l1 (f : Fin (m + 1) → ℝ) : ℝ := ∑ a, |f a|

/-- The action of a kernel on a measure: `(μ Q) b = ∑ₐ μ a · Q a b`. -/
def apply (Q : Fin (m + 1) → Fin (m + 1) → ℝ) (μ : Fin (m + 1) → ℝ) :
    Fin (m + 1) → ℝ :=
  fun b => ∑ a, μ a * Q a b

/-- A probability vector. -/
def Target (π : Fin (m + 1) → ℝ) : Prop := (∀ b, 0 ≤ π b) ∧ ∑ b, π b = 1

/-- The Doeblin minorant relative to `π`. -/
def Minorant (Q : Fin (m + 1) → Fin (m + 1) → ℝ) (π : Fin (m + 1) → ℝ) (ε : ℝ) : Prop :=
  ∀ a b, ε * π b ≤ Q a b

/-- `π` is stationary for `Q` (`π Q = π`). -/
def Stationary (Q : Fin (m + 1) → Fin (m + 1) → ℝ) (π : Fin (m + 1) → ℝ) : Prop :=
  ∀ b, ∑ a, π a * Q a b = π b

theorem l1_nonneg (f : Fin (m + 1) → ℝ) : 0 ≤ l1 f :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_le_l1 (f : Fin (m + 1) → ℝ) (b : Fin (m + 1)) : |f b| ≤ l1 f := by
  refine Finset.single_le_sum (f := fun a => |f a|) (fun a _ => abs_nonneg _) (mem_univ b)

/-- The constant part of the minorant cancels: on a signed measure of zero total mass, the kernel
acts through `Q a b − ε π b`. -/
theorem apply_eq_sum_sub {π : Fin (m + 1) → ℝ} (Q : Fin (m + 1) → Fin (m + 1) → ℝ)
    (ε : ℝ) {σ : Fin (m + 1) → ℝ} (hσ : ∑ a, σ a = 0) (b : Fin (m + 1)) :
    apply Q σ b = ∑ a, σ a * (Q a b - ε * π b) := by
  simp only [apply]
  have : ∑ a, σ a * (Q a b - ε * π b) = ∑ a, σ a * Q a b - ε * π b * ∑ a, σ a := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [this, hσ, mul_zero, sub_zero]

/-- The one-step Doeblin estimate: the kernel scales the `ℓ¹` mass of a zero-total signed measure
by at most `1 − ε`. -/
theorem sum_abs_sub_minorant {Q : Fin (m + 1) → Fin (m + 1) → ℝ}
    {π : Fin (m + 1) → ℝ} {ε : ℝ} (hrow : RowStoch Q) (hmin : Minorant Q π ε)
    (hπ : Target π) (a : Fin (m + 1)) :
    ∑ b, |Q a b - ε * π b| = 1 - ε := by
  have hnn : ∀ b, 0 ≤ Q a b - ε * π b := fun b => by
    have := hmin a b
    linarith
  calc ∑ b, |Q a b - ε * π b| = ∑ b, (Q a b - ε * π b) := by
        exact Finset.sum_congr rfl fun b _ => abs_of_nonneg (hnn b)
    _ = 1 - ε := by
        rw [Finset.sum_sub_distrib, hrow a, ← Finset.mul_sum, hπ.2, mul_one]

theorem eps_le_one {Q : Fin (m + 1) → Fin (m + 1) → ℝ} {π : Fin (m + 1) → ℝ} {ε : ℝ}
    (hrow : RowStoch Q) (hmin : Minorant Q π ε) (hπ : Target π) : ε ≤ 1 := by
  have h1 : ε * (∑ b, π b) ≤ ∑ b, Q 0 b := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => hmin 0 b
  rwa [hπ.2, hrow 0, mul_one] at h1

theorem l1_apply_le {Q : Fin (m + 1) → Fin (m + 1) → ℝ} {π : Fin (m + 1) → ℝ} {ε : ℝ}
    (hrow : RowStoch Q) (hmin : Minorant Q π ε) (hπ : Target π)
    {σ : Fin (m + 1) → ℝ} (hσ : ∑ a, σ a = 0) :
    l1 (apply Q σ) ≤ (1 - ε) * l1 σ := by
  have hstep : ∀ b, |apply Q σ b| ≤ ∑ a, |σ a| * |Q a b - ε * π b| := by
    intro b
    rw [apply_eq_sum_sub Q ε hσ b]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [abs_mul]
  calc l1 (apply Q σ) = ∑ b, |apply Q σ b| := rfl
    _ ≤ ∑ b, ∑ a, |σ a| * |Q a b - ε * π b| := Finset.sum_le_sum fun b _ => hstep b
    _ = ∑ a, ∑ b, |σ a| * |Q a b - ε * π b| := Finset.sum_comm
    _ = ∑ a, |σ a| * ∑ b, |Q a b - ε * π b| := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ a, |σ a| * (1 - ε) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [sum_abs_sub_minorant hrow hmin hπ a]
    _ = (∑ a, |σ a|) * (1 - ε) := (Finset.sum_mul _ _ _).symm
    _ = (1 - ε) * l1 σ := by rw [l1, mul_comm]

/-- A row-stochastic kernel preserves the total mass. -/
theorem sum_apply {Q : Fin (m + 1) → Fin (m + 1) → ℝ} (hrow : RowStoch Q)
    (μ : Fin (m + 1) → ℝ) : ∑ b, apply Q μ b = ∑ a, μ a := by
  simp only [apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.mul_sum, hrow a, mul_one]

theorem l1_apply_iter_le {Q : Fin (m + 1) → Fin (m + 1) → ℝ} {π : Fin (m + 1) → ℝ} {ε : ℝ}
    (hrow : RowStoch Q) (hmin : Minorant Q π ε) (hπ : Target π)
    {σ : Fin (m + 1) → ℝ} (hσ : ∑ a, σ a = 0) (n : ℕ) :
    l1 ((apply Q)^[n] σ) ≤ (1 - ε) ^ n * l1 σ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hσn : ∑ a, ((apply Q)^[n] σ) a = 0 := by
      rw [show (∑ a, ((apply Q)^[n] σ) a) = ∑ a, σ a from ?_, hσ]
      clear hσ ih
      induction n with
      | zero => simp
      | succ n ih' => rw [Function.iterate_succ_apply', sum_apply hrow, ih']
    rw [Function.iterate_succ_apply', pow_succ]
    calc l1 (apply Q ((apply Q)^[n] σ))
        ≤ (1 - ε) * l1 ((apply Q)^[n] σ) := l1_apply_le hrow hmin hπ hσn
      _ ≤ (1 - ε) * ((1 - ε) ^ n * l1 σ) := by
          refine mul_le_mul_of_nonneg_left ih ?_
          linarith [eps_le_one hrow hmin hπ]
      _ = (1 - ε) ^ n * (1 - ε) * l1 σ := by ring

theorem apply_stationary {Q : Fin (m + 1) → Fin (m + 1) → ℝ} {π : Fin (m + 1) → ℝ}
    (hstat : Stationary Q π) : apply Q π = π :=
  funext hstat

theorem apply_sub (Q : Fin (m + 1) → Fin (m + 1) → ℝ) (f g : Fin (m + 1) → ℝ) :
    apply Q (f - g) = apply Q f - apply Q g := by
  funext b
  simp only [apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem iterate_sub_stationary {Q : Fin (m + 1) → Fin (m + 1) → ℝ} {π : Fin (m + 1) → ℝ}
    (hstat : Stationary Q π) (f : Fin (m + 1) → ℝ) (n : ℕ) :
    (apply Q)^[n] (f - π) = (apply Q)^[n] f - π := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, apply_sub,
      apply_stationary hstat]

/-- **Convergence to the prescribed target.**  A row-stochastic kernel with a Doeblin minorant
`ε π` relative to `π`, for which `π` is stationary, drives every starting probability vector to
`π` in `ℓ¹`, at the geometric rate `1 − ε`. -/
theorem tendsto_iter_target {Q : Fin (m + 1) → Fin (m + 1) → ℝ} {π : Fin (m + 1) → ℝ} {ε : ℝ}
    (hrow : RowStoch Q) (hmin : Minorant Q π ε) (hπ : Target π) (hstat : Stationary Q π)
    (hε0 : 0 < ε) {f : Fin (m + 1) → ℝ} (hf : ∑ a, f a = 1) :
    Tendsto (fun n => l1 ((apply Q)^[n] f - π)) atTop (𝓝 0) := by
  have hσ : ∑ a, (f - π) a = 0 := by
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib, hf, hπ.2, sub_self]
  have hnonneg : 0 ≤ 1 - ε := by linarith [eps_le_one hrow hmin hπ]
  have hlt : 1 - ε < 1 := by linarith
  have hbound : ∀ n, l1 ((apply Q)^[n] f - π) ≤ (1 - ε) ^ n * l1 (f - π) := by
    intro n
    rw [← iterate_sub_stationary hstat f n]
    exact l1_apply_iter_le hrow hmin hπ hσ n
  refine squeeze_zero (fun n => l1_nonneg _) hbound ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hnonneg hlt).mul_const (l1 (f - π))

/-- `ℓ¹` convergence implies pointwise convergence. -/
theorem tendsto_iter_target_pointwise {Q : Fin (m + 1) → Fin (m + 1) → ℝ}
    {π : Fin (m + 1) → ℝ} {ε : ℝ} (hrow : RowStoch Q) (hmin : Minorant Q π ε)
    (hπ : Target π) (hstat : Stationary Q π) (hε0 : 0 < ε) {f : Fin (m + 1) → ℝ}
    (hf : ∑ a, f a = 1) (b : Fin (m + 1)) :
    Tendsto (fun n => ((apply Q)^[n] f) b) atTop (𝓝 (π b)) := by
  have h0 := tendsto_iter_target hrow hmin hπ hstat hε0 hf
  have hb : ∀ n, |((apply Q)^[n] f - π) b| ≤ l1 ((apply Q)^[n] f - π) := by
    intro n
    rw [← iterate_sub_stationary hstat f n]
    exact abs_le_l1 ((apply Q)^[n] (f - π)) b
  have habs : Tendsto (fun n => |((apply Q)^[n] f - π) b|) atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _) hb h0
  have hz : Tendsto (fun n => ((apply Q)^[n] f - π) b) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using habs
  have hfin : Tendsto (fun n => ((apply Q)^[n] f - π) b + π b) atTop (𝓝 (0 + π b)) :=
    hz.add_const (π b)
  simpa [sub_add_cancel] using hfin

/-! ### The concrete pCNL-type kernel with a prescribed target -/

/-- The Metropolis-type kernel of the proposal `π` with hold mass `1 − ε`: at each step hold with
probability `1 − ε`, otherwise draw from `π`.  Since every entry is at least `ε π b`, its Doeblin
minorant is `ε` by construction. -/
def targetKernel (ε : ℝ) (π : Fin (m + 1) → ℝ) : Fin (m + 1) → Fin (m + 1) → ℝ :=
  fun a b => ε * π b + if b = a then 1 - ε else 0

theorem targetKernel_rowStoch {π : Fin (m + 1) → ℝ} (hπ : Target π) (ε : ℝ) :
    RowStoch (targetKernel ε π) := by
  intro a
  have h1 : (∑ b : Fin (m + 1), (if b = a then 1 - ε else (0 : ℝ))) = 1 - ε := by
    rw [Finset.sum_ite_eq']
    simp
  calc ∑ b : Fin (m + 1), targetKernel ε π a b
      = ∑ b : Fin (m + 1), (ε * π b + if b = a then 1 - ε else (0 : ℝ)) := rfl
    _ = ε * (∑ b, π b) + ∑ b : Fin (m + 1), (if b = a then 1 - ε else (0 : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = ε * 1 + (1 - ε) := by rw [hπ.2, h1]
    _ = 1 := by ring

theorem targetKernel_minorant {π : Fin (m + 1) → ℝ} (hπ : Target π) {ε : ℝ} (hε1 : ε ≤ 1) :
    Minorant (targetKernel ε π) π ε := by
  intro a b
  have hp := hπ.1 b
  simp only [targetKernel]
  split_ifs with h
  · linarith
  · linarith

theorem targetKernel_stationary {π : Fin (m + 1) → ℝ} (hπ : Target π) (ε : ℝ) :
    Stationary (targetKernel ε π) π := by
  intro b
  have h1 : ∑ a : Fin (m + 1), π a * (if b = a then 1 - ε else (0 : ℝ)) = π b * (1 - ε) := by
    have hsplit : ∀ a : Fin (m + 1),
        π a * (if b = a then 1 - ε else (0 : ℝ)) = if b = a then π a * (1 - ε) else 0 := by
      intro a
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_ite_eq]
    simp
  calc ∑ a : Fin (m + 1), π a * targetKernel ε π a b
      = ∑ a : Fin (m + 1),
          (π a * (ε * π b) + π a * (if b = a then 1 - ε else (0 : ℝ))) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [targetKernel]
        ring
    _ = ε * π b * (∑ a, π a) + ∑ a : Fin (m + 1), π a * (if b = a then 1 - ε else (0 : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun a _ => by ring
    _ = ε * π b * 1 + π b * (1 - ε) := by rw [hπ.2, h1]
    _ = π b := by ring

/-- **Convergence to the pCNL invariant measure `π`.**  For the kernel that holds with mass
`1 − ε` and otherwise draws from `π`, every starting probability vector converges to `π` in `ℓ¹` at
the geometric rate `1 − ε`. -/
theorem tendsto_iter_targetKernel {π : Fin (m + 1) → ℝ} (hπ : Target π) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) {f : Fin (m + 1) → ℝ} (hf : ∑ a, f a = 1) :
    Tendsto (fun n => l1 ((apply (targetKernel ε π))^[n] f - π)) atTop (𝓝 0) :=
  tendsto_iter_target (targetKernel_rowStoch hπ ε) (targetKernel_minorant hπ hε1) hπ
    (targetKernel_stationary hπ ε) hε0 hf

/-- The pointwise form of the same convergence. -/
theorem tendsto_iter_targetKernel_apply {π : Fin (m + 1) → ℝ} (hπ : Target π) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) {f : Fin (m + 1) → ℝ} (hf : ∑ a, f a = 1)
    (b : Fin (m + 1)) :
    Tendsto (fun n => (((apply (targetKernel ε π))^[n] f) b)) atTop (𝓝 (π b)) :=
  tendsto_iter_target_pointwise (targetKernel_rowStoch hπ ε) (targetKernel_minorant hπ hε1) hπ
    (targetKernel_stationary hπ ε) hε0 hf b

/-- **§22 is the uniform-target case of this kernel.**  With `π` uniform and `ε = (m+1)t` the
targeted kernel *is* `uniformStep t`, so the doubly stochastic cone model is the special case in
which the target happens to be flat. -/
theorem uniformStep_eq_targetKernel (m : ℕ) (t : ℝ) :
    uniformStep (m := m) t
      = targetKernel (m := m) (((m : ℝ) + 1) * t) (fun _ => 1 / ((m : ℝ) + 1)) := by
  funext a b
  have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hc : ((m : ℝ) + 1) * t * (1 / ((m : ℝ) + 1)) = t := by
    field_simp
  simp only [uniformStep, targetKernel, hc]



end BookProof.MCMC.PositivityCone

/-! ## Wiring into the Module 4–5 gap bound

`BookProof.MCMC.UnadjustedPCN.pcn_geometric_ergodicity` needs three hypotheses on the step: it
fixes the invariant state (`hfix`), it contracts the orthogonal complement by `ρ` (`hgap`), and the
gap `γ = 1 − ρ` is positive.  §18 supplies all three on the core — `baseOp_vac`,
`coreNorm_baseOp_sector_le` and `ρ ≤ 1` — so the pCNL gap hypothesis can cite the contraction facts
rather than assume them.
-/

namespace BookProof.MCMC.FockLangevin

open BookProof.ReferenceGap BookProof.MCMC.UnadjustedPCN

variable {d : ℕ}

/-- The `hgap` shape of Module 4–5, cited from §18: `P₀` contracts the non-vacuum sector by `ρ`. -/
theorem module45_gap_hypothesis {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    ∀ c : CoreCoeff d, (∀ n ∈ c.support, 1 ≤ natDeg n) →
      coreNorm (baseOp ρ c) ≤ ρ * coreNorm c :=
  fun _c hc => coreNorm_baseOp_sector_le h0 h1 hc

/-- The `hfix` shape of Module 4–5, cited from §18: `P₀` fixes the vacuum, the invariant state. -/
theorem module45_invariant_state (d : ℕ) (ρ : ℝ) :
    baseOp ρ (Finsupp.single (0 : Fin d → ℕ) 1) = Finsupp.single (0 : Fin d → ℕ) 1 :=
  baseOp_vac ρ

/-- The gap `γ = 1 − ρ` is positive below `ρ = 1`. -/
theorem module45_gap_positive {ρ : ℝ} (hρ : ρ < 1) : 0 < 1 - ρ := by linarith

/-- **The Module 4–5 hypotheses, discharged on the core.**  The three inputs
`pcn_geometric_ergodicity` asks for are §18's contraction, §18's fixed vacuum and the positivity of
the gap — no pCNL gap hypothesis is left to assume. -/
theorem module45_hypotheses_cited (d : ℕ) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (hρ : ρ < 1) :
    (∀ c : CoreCoeff d, (∀ n ∈ c.support, 1 ≤ natDeg n) →
        coreNorm (baseOp ρ c) ≤ ρ * coreNorm c)
      ∧ 0 < 1 - ρ
      ∧ baseOp ρ (Finsupp.single (0 : Fin d → ℕ) 1) = Finsupp.single (0 : Fin d → ℕ) 1 :=
  ⟨module45_gap_hypothesis h0 h1, module45_gap_positive hρ, module45_invariant_state d ρ⟩

/-- The iterate bound those hypotheses produce — the core form of
`pcn_geometric_ergodicity`'s conclusion `‖Pᵐ ψ‖ ≤ ρᵐ‖ψ‖`. -/
theorem module45_iterate_bound {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {c : CoreCoeff d}
    (hc : ∀ n ∈ c.support, 1 ≤ natDeg n) (m : ℕ) :
    coreNorm ((baseOp ρ)^[m] c) ≤ ρ ^ m * coreNorm c :=
  coreNorm_iter_baseOp_le h0 h1 hc m

end BookProof.MCMC.FockLangevin
