import Mathlib

/-!
# S3: the independent short-distance exclusion, in finite-kernel form

Work order: `SM_ESA_COMPLETION_PLAN.md` P0 (`TraceTest` as the template), `softmodes.md`
"Second reading (2026-11-11)" B–C, `cftproof.md` "Second reading" C.

## What is excluded, and what is not

The external non-freeness result excludes a **finite list of explicit mass-shell modes** at short
distance, not a class of theories.  Its test is that a fixed multiple of `r^8 log²(1/r)` fails to
converge to the correlator's coefficient.  This module states the same exclusion here, in that
finite form, on our own kernel shape:

* `modeKernel` is one mode, `c · E^t · exp(−rE)` — the external `(1/2E) E^timeOrder num(p) exp(−rE)`
  with `p` fixed, so that `(1/2E) E^timeOrder num(p)` is a single complex coefficient `c`, `t` is
  the time degree, and `E` the mode energy (their `sqrt(m² + ‖p‖²)`, an ansatz parameter there);
* `wickSum` is a finite sum of such modes over a `Finset`, the `List` of `TraceTest`;
* `not_eventuallyEq_wickSum` **is** the exclusion: a function whose normalised short-distance limit
  is a nonzero `c` is not eventually equal to any such finite sum.

Two properties of the external statement are reproduced deliberately.  The exclusion is a
short-distance asymptotic of an explicit function, so it is stateable **without constructing an OS
Hamiltonian** — no gap, no mode space, no long-distance decay is used.  And the normalisation is
carried by an explicit factor rather than a bare inequality, because the dimensional content lives
in that factor: two grade-4 insertions have `weight = 4 + 4 = 8`, which is the `r^8` exponent.

## The honesty boundary

* `not_eventuallyEq_wickSum` takes the nonzero limit of `shortNorm · F` as a **hypothesis**.  That
  limit is the physical input: this module does not compute the trace coefficient of any model, and
  in particular does not prove that our `K_SM` has one.
* The excluded family is finite lists of `modeKernel`s.  It is **not** "every generalized free
  field": the external README places general exclusion of continuous-mass generalized free fields
  out of scope, and this module inherits that limit rather than closing it.
* Nothing here is a spectral claim.  `modeKernel`'s `E` is a free parameter, so a result about it is
  a statement about an ansatz, never about the interacting spectrum.
-/

namespace BookProof.SmFreeModeExclusion

open Filter Topology

/-- The short-distance normalisation of a grade-8 label: `r^8 log²(1/r)`.  The exponent is the
weight of the two grade-4 insertions (`weight a = ∑ i, (a i).1`), not a fitted constant. -/
noncomputable def shortNorm (r : ℝ) : ℝ := r ^ 8 * Real.log (1 / r) ^ 2

/-- One mass-shell mode at fixed momentum: `c · E^t · exp(−rE)`.  `E > 0` is the mode energy, `t`
the time degree, `c` the coefficient `(1/2E) E^timeOrder num(p)` at the fixed momentum. -/
noncomputable def modeKernel (E : ℝ) (t : ℕ) (c : ℂ) (r : ℝ) : ℂ :=
  c * (E ^ t : ℂ) * Complex.exp (-((r : ℂ) * (E : ℂ)))

/-- A finite Wick sum: a finite set of modes.  This is the `List (ℂ × Track)` of the external test,
in the form our sums take. -/
noncomputable def wickSum {ι : Type*} (s : Finset ι) (K : ι → ℝ → ℂ) : ℝ → ℂ :=
  fun r => ∑ i ∈ s, K i r

/-! ## The normalisation kills one mode

`r^8 log²(1/r) → 0`, faster than any inverse power, so it beats the polynomial-`E` prefactor; the
exponential factor tends to `1` and therefore changes nothing.  Both factors have finite limits, so
this is `Tendsto.mul` and not a squeeze argument. -/

/-- `r^8 log² r → 0` at `0⁺`: from Mathlib's `log x · x → 0`, squared to `r² log² r → 0`, times
`r⁶ → 0`. -/
theorem tendsto_pow_log_sq :
    Tendsto (fun r : ℝ => r ^ 8 * Real.log r ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hsq : Tendsto (fun r : ℝ => r ^ 2 * Real.log r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_log_mul_rpow_nhdsGT_zero (r := (1 : ℝ)) one_pos).pow 2
    have heq : (fun x : ℝ => (Real.log x * x ^ (1 : ℝ)) ^ 2)
        =ᶠ[𝓝[>] (0 : ℝ)] fun x => x ^ 2 * Real.log x ^ 2 := by
      filter_upwards with x
      rw [mul_pow, Real.rpow_one]
      ring
    have h' := h.congr' heq
    simpa using h'
  have h6 : Tendsto (fun r : ℝ => r ^ 6) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => r ^ 6) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) ^ 6)) :=
      (continuous_pow 6).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have heq : (fun r : ℝ => r ^ 2 * Real.log r ^ 2 * r ^ 6)
      =ᶠ[𝓝[>] (0 : ℝ)] fun r => r ^ 8 * Real.log r ^ 2 := by
    filter_upwards with r
    ring
  have h' := (hsq.mul h6).congr' heq
  simpa using h'

/-- The same where the logarithm is written as `log (1/r)`, the external form. -/
theorem tendsto_pow_log_inv_sq :
    Tendsto (fun r : ℝ => r ^ 8 * Real.log (1 / r) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have heq : (fun r : ℝ => r ^ 8 * Real.log r ^ 2)
      =ᶠ[𝓝[>] (0 : ℝ)] fun r => r ^ 8 * Real.log (1 / r) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [one_div, Real.log_inv, neg_sq]
  exact tendsto_pow_log_sq.congr' heq

/-- The exponential factor of a mode tends to `1`: the mode energy is fixed and `r → 0`. -/
theorem tendsto_mode_exp (E : ℝ) :
    Tendsto (fun r : ℝ => Complex.exp (-((r : ℂ) * (E : ℂ)))) (𝓝[>] 0) (𝓝 1) := by
  have hlin : Tendsto (fun r : ℝ => -((r : ℂ) * (E : ℂ))) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => -((r : ℂ) * (E : ℂ))) (𝓝 (0 : ℝ))
        (𝓝 (-(((0 : ℝ) : ℂ) * (E : ℂ)))) :=
      ((Complex.continuous_ofReal.mul continuous_const).neg).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have h := (Complex.continuous_exp.tendsto (0 : ℂ)).comp hlin
  simpa using h

/-- **The normalisation kills one mode.**  `r^8 log²(1/r) · modeKernel E t c r → 0` for every
energy, degree and coefficient — the analytic fact the exclusion rests on. -/
theorem tendsto_shortNorm_modeKernel (E : ℝ) (t : ℕ) (c : ℂ) :
    Tendsto (fun r : ℝ => (shortNorm r : ℂ) * modeKernel E t c r) (𝓝[>] 0) (𝓝 0) := by
  -- The normalised factor alone, then the mode's constant coefficient.
  have hnorm : Tendsto (fun r : ℝ => (shortNorm r : ℂ)
      * Complex.exp (-((r : ℂ) * (E : ℂ)))) (𝓝[>] 0) (𝓝 0) := by
    have hof : Tendsto (fun r : ℝ => ((r ^ 8 * Real.log (1 / r) ^ 2 : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 0) := by
      have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp tendsto_pow_log_inv_sq
      have h0 : ((0 : ℝ) : ℂ) = 0 := by simp
      rwa [h0] at h
    have heq : (fun r : ℝ => ((r ^ 8 * Real.log (1 / r) ^ 2 : ℝ) : ℂ))
        =ᶠ[𝓝[>] (0 : ℝ)] fun r => (shortNorm r : ℂ) := by
      filter_upwards with r
      simp only [shortNorm]
    have hlog : Tendsto (fun r : ℝ => (shortNorm r : ℂ)) (𝓝[>] 0) (𝓝 0) := hof.congr' heq
    simpa using hlog.mul (tendsto_mode_exp E)
  have hconst : Tendsto (fun r : ℝ => (c * (E ^ t : ℂ))
      * ((shortNorm r : ℂ) * Complex.exp (-((r : ℂ) * (E : ℂ))))) (𝓝[>] 0) (𝓝 0) := by
    have h := hnorm.const_mul (c * (E ^ t : ℂ))
    simpa using h
  have heq : (fun r : ℝ => (c * (E ^ t : ℂ))
      * ((shortNorm r : ℂ) * Complex.exp (-((r : ℂ) * (E : ℂ)))))
      =ᶠ[𝓝[>] (0 : ℝ)] fun r => (shortNorm r : ℂ) * modeKernel E t c r := by
    filter_upwards with r
    simp only [modeKernel]
    ring
  exact hconst.congr' heq

/-! ## The finite sum, and the exclusion -/

/-- A finite sum of modes is still killed by the normalisation. -/
theorem tendsto_shortNorm_wickSum {ι : Type*} (s : Finset ι) (K : ι → ℝ → ℂ)
    (hK : ∀ i ∈ s, Tendsto (fun r : ℝ => (shortNorm r : ℂ) * K i r) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ => (shortNorm r : ℂ) * wickSum s K r) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_finset_sum s (fun i hi => hK i hi)
  have hzero : (∑ i ∈ s, (0 : ℂ)) = 0 := by simp
  rw [hzero] at h
  have heq : (fun r : ℝ => ∑ i ∈ s, (shortNorm r : ℂ) * K i r)
      =ᶠ[𝓝[>] (0 : ℝ)] fun r => (shortNorm r : ℂ) * wickSum s K r := by
    filter_upwards with r
    simp only [wickSum, Finset.mul_sum]
  exact h.congr' heq

/-- **The independent spectral exclusion, in finite-kernel form.**  If the normalised
short-distance limit of `F` is a nonzero `c`, then `F` is not eventually equal to any finite sum of
mass-shell modes.  The hypothesis `hF` is the physical coefficient; `hK` is discharged modewise by
`tendsto_shortNorm_modeKernel`. -/
theorem not_eventuallyEq_wickSum {ι : Type*} {F : ℝ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (s : Finset ι) (K : ι → ℝ → ℂ)
    (hK : ∀ i ∈ s, Tendsto (fun r : ℝ => (shortNorm r : ℂ) * K i r) (𝓝[>] 0) (𝓝 0))
    (hF : Tendsto (fun r : ℝ => (shortNorm r : ℂ) * F r) (𝓝[>] 0) (𝓝 c)) :
    ¬ (F =ᶠ[𝓝[>] 0] wickSum s K) := by
  intro hEq
  have hzero := tendsto_shortNorm_wickSum s K hK
  have hsame : (fun r : ℝ => (shortNorm r : ℂ) * F r)
      =ᶠ[𝓝[>] 0] fun r : ℝ => (shortNorm r : ℂ) * wickSum s K r := by
    filter_upwards [hEq] with r hr
    rw [hr]
  have hlim : Tendsto (fun r : ℝ => (shortNorm r : ℂ) * F r) (𝓝[>] 0) (𝓝 0) :=
    hzero.congr' hsame.symm
  exact hc (tendsto_nhds_unique hlim hF).symm

/-- The same exclusion with the kernel family spelled out: a finite family of energies, degrees and
coefficients, evaluated at our `modeKernel`.  This is the shape an S3 statement takes at a concrete
candidate correlator. -/
theorem not_eventuallyEq_modeKernels {ι : Type*} {F : ℝ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (s : Finset ι) (E : ι → ℝ) (t : ι → ℕ) (co : ι → ℂ)
    (hF : Tendsto (fun r : ℝ => (shortNorm r : ℂ) * F r) (𝓝[>] 0) (𝓝 c)) :
    ¬ (F =ᶠ[𝓝[>] 0] fun r => ∑ i ∈ s, modeKernel (E i) (t i) (co i) r) :=
  not_eventuallyEq_wickSum hc s (fun i => modeKernel (E i) (t i) (co i))
    (fun i _ => tendsto_shortNorm_modeKernel (E i) (t i) (co i)) hF

end BookProof.SmFreeModeExclusion
