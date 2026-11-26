import Mathlib

/-!
# Chapter ExternalSourceLimitOrder — H6 Route B, strict limit order

H6 Route B requires the non-commuting limits
`lim_{J→0+} lim_{V→∞} ⟨φ⟩ = v ≠ 0` versus `lim_{V→∞} lim_{J→0+} ⟨φ⟩ = 0`.
This module proves them on a finite-volume benchmark: the saturated response
`m_V(J) = v · (V·J)/(1 + V·J)`, the elementary magnetization of a spin in a field whose
effective coupling grows with the number of modes.  It is a benchmark, not the physical
Higgs/φ⁴ expectation; the lift to the nested-Fock measure is separate work.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace BookProof.ExternalSourceLimitOrder

open Filter Topology

/-- Finite-volume magnetization at source strength `J ≥ 0` and volume parameter `V`. -/
def finiteMagnet (V : ℕ) (J v : ℝ) : ℝ := v * ((V : ℝ) * J / (1 + (V : ℝ) * J))

/-- At fixed positive source the magnetization tends to `v` as the volume grows. -/
theorem tendsto_finiteMagnet_atTop {J v : ℝ} (hJ : 0 < J) :
    Tendsto (fun V : ℕ => finiteMagnet V J v) atTop (𝓝 v) := by
  have hden : ∀ V : ℕ, 1 + (V : ℝ) * J ≠ 0 := by
    intro V
    have hpos : 0 < 1 + (V : ℝ) * J := by positivity
    exact ne_of_gt hpos
  have hfrac : ∀ V : ℕ, (V : ℝ) * J / (1 + (V : ℝ) * J) =
      1 - (1 + (V : ℝ) * J)⁻¹ := by
    intro V
    field_simp [hden V]
    ring
  simp_rw [finiteMagnet, hfrac]
  have hinv : Tendsto (fun V : ℕ => (1 + (V : ℝ) * J)⁻¹) atTop (𝓝 0) := by
    have hmul : Tendsto (fun V : ℕ => (V : ℝ) * J) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hJ
    have hadd' : Tendsto (fun V : ℕ => (V : ℝ) * J + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 hmul
    have hadd : Tendsto (fun V : ℕ => 1 + (V : ℝ) * J) atTop atTop := by
      simpa [add_comm] using hadd'
    exact tendsto_inv_atTop_zero.comp hadd
  have hone : Tendsto (fun V : ℕ => (1 : ℝ) - (1 + (V : ℝ) * J)⁻¹) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hinv
  simpa using (hone.const_mul v)

/-- At fixed volume the magnetization tends to zero as the source is removed from above. -/
theorem tendsto_finiteMagnet_nhdsWithin_zero (V : ℕ) (v : ℝ) :
    Tendsto (fun J : ℝ => finiteMagnet V J v) (𝓝[>] 0) (𝓝 0) := by
  have hden : ∀ᶠ J in 𝓝[>] (0 : ℝ), 1 + (V : ℝ) * J ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with J hJ
    have hpos : 0 ≤ (V : ℝ) * J := mul_nonneg (Nat.cast_nonneg _) (le_of_lt hJ)
    exact ne_of_gt (by linarith)
  have hnum' : Tendsto (fun J : ℝ => (V : ℝ) * J) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa using ((continuousAt_const (x := (0 : ℝ)) (y := (V : ℝ))).mul continuousAt_id).tendsto
  have hnum : Tendsto (fun J : ℝ => (V : ℝ) * J) (𝓝[>] 0) (𝓝 0) :=
    hnum'.mono_left inf_le_left
  have hdenlim : Tendsto (fun J : ℝ => 1 + (V : ℝ) * J) (𝓝[>] 0) (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hnum : Tendsto (fun J : ℝ => (1 : ℝ) + (V : ℝ) * J)
      (𝓝[>] 0) (𝓝 (1 + 0)))
  have hfrac : Tendsto (fun J : ℝ => (V : ℝ) * J / (1 + (V : ℝ) * J))
      (𝓝[>] 0) (𝓝 (0 / 1)) := hnum.div hdenlim (by norm_num)
  simpa [finiteMagnet] using hfrac.const_mul v

/-- The two limit orders disagree: removing the source after taking the volume limit leaves a
    nonzero VEV, while taking the volume limit after removing the source leaves zero. -/
theorem limit_order_noncommute {v : ℝ} (hv : v ≠ 0) :
    (∀ J : ℝ, 0 < J → Tendsto (fun V : ℕ => finiteMagnet V J v) atTop (𝓝 v)) ∧
      (∀ V : ℕ, Tendsto (fun J : ℝ => finiteMagnet V J v) (𝓝[>] 0) (𝓝 0)) ∧
        (0 : ℝ) ≠ v := by
  refine ⟨?_, ?_, hv.symm⟩
  · intro J hJ
    exact tendsto_finiteMagnet_atTop hJ
  · intro V
    exact tendsto_finiteMagnet_nhdsWithin_zero V v

end BookProof.ExternalSourceLimitOrder
