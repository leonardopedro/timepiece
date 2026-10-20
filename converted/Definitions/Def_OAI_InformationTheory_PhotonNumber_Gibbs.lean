/-
prove2.me platform library module `Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_InformationTheory_PhotonNumber_Gibbs.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Gibbs.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntropyPhotonNumber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace TraceEnsemble

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

def positiveRoot (T : E →L[ℂ] E) : E →L[ℂ] E := CFC.sqrt T

def operator (v : I → E) : E →L[ℂ] E :=
  ∑' i, InnerProductSpace.rankOne ℂ (v i) (v i)

theorem summable_rankOne {v : I → E} (hv : Summable (fun i => ‖v i‖^2)) :
    Summable (fun i => InnerProductSpace.rankOne ℂ (v i) (v i)) := by
  apply Summable.of_norm
  simpa only [InnerProductSpace.norm_rankOne, pow_two] using hv

theorem hasSum_rankOne {v : I → E} (hv : Summable (fun i => ‖v i‖^2)) :
    HasSum (fun i => InnerProductSpace.rankOne ℂ (v i) (v i)) (operator v) :=
  (summable_rankOne hv).hasSum

theorem positive {v : I → E} (_hv : Summable (fun i => ‖v i‖^2)) :
    (operator v).IsPositive := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mp
  exact tsum_nonneg (fun i => (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (InnerProductSpace.isPositive_rankOne_self (v i)))

theorem hasSum_entry {v : I → E} (hv : Summable (fun i => ‖v i‖^2)) (x y : E) :
    HasSum (fun i => inner ℂ x (v i) * inner ℂ (v i) y)
      (inner ℂ x (operator v y)) := by
  convert ((hasSum_rankOne hv).mapL (ContinuousLinearMap.apply ℂ E y)).mapL (innerSL ℂ x) using 1
  ext i
  simp [InnerProductSpace.rankOne_apply, mul_comm]

theorem hasSum_quadratic {v : I → E} (hv : Summable (fun i => ‖v i‖^2)) (x : E) :
    HasSum (fun i => ‖inner ℂ x (v i)‖^2) (inner ℂ x (operator v x)).re := by
  convert (hasSum_entry hv x x).mapL Complex.reCLM using 1
  ext i
  rw [← inner_conj_symm (v i) x, Complex.mul_conj]
  simp only [Complex.reCLM_apply, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

omit [CompleteSpace E] in
theorem basis_hasSum_norm_sq (b : HilbertBasis J ℂ E) (x : E) :
    HasSum (fun j => ‖inner ℂ (b j) x‖^2) (‖x‖^2) := by
  have h := (b.hasSum_inner_mul_inner x x).mapL Complex.reCLM
  convert h using 1
  · ext j
    simp only [Complex.reCLM_apply]
    conv_rhs => rw [← inner_conj_symm x (b j), Complex.conj_mul']
    simp [← Complex.ofReal_pow]
  · simp [← Complex.ofReal_pow]

theorem trace {v : I → E} {t : ℝ} (hv : HasSum (fun i => ‖v i‖^2) t)
    (b : HilbertBasis J ℂ E) :
    HasSum (fun j => (inner ℂ (b j) (operator v (b j))).re) t := by
  have hparse (i : I) : (∑' j, ‖inner ℂ (b j) (v i)‖^2) = ‖v i‖^2 :=
    (basis_hasSum_norm_sq b (v i)).tsum_eq
  have hd : Summable (fun a : I × J => ‖inner ℂ (b a.2) (v a.1)‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun i => (basis_hasSum_norm_sq b (v i)).summable, ?_⟩
    simpa only [hparse] using hv.summable
  have he : (∑' j, ∑' i, ‖inner ℂ (b j) (v i)‖^2) = t := by
    calc
      _ = ∑' i, ∑' j, ‖inner ℂ (b j) (v i)‖^2 :=
        Summable.tsum_comm (f := fun i j => ‖inner ℂ (b j) (v i)‖^2) hd
      _ = t := by simpa only [hparse] using hv.tsum_eq
  have hquad (j : J) : (∑' i, ‖inner ℂ (b j) (v i)‖^2) =
      (inner ℂ (b j) (operator v (b j))).re := (hasSum_quadratic hv.summable (b j)).tsum_eq
  have hh : Summable (fun j => ∑' i, ‖inner ℂ (b j) (v i)‖^2) := hd.prod_symm.prod
  exact he ▸ (by simpa only [hquad] using hh.hasSum)

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

omit [CompleteSpace E] in
theorem summable_entry_norm {v : I → E} (hv : Summable (fun i => ‖v i‖^2)) (x y : E) :
    Summable (fun i => ‖inner ℂ x (v i)*inner ℂ (v i) y‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hv.mul_left (‖x‖*‖y‖))
  intro i
  calc
    _ = ‖inner ℂ x (v i)‖*‖inner ℂ (v i) y‖ := norm_mul _ _
    _ ≤ (‖x‖*‖v i‖)*(‖v i‖*‖y‖) :=
      mul_le_mul (norm_inner_le_norm _ _) (norm_inner_le_norm _ _) (norm_nonneg _) (by positivity)
    _ = (‖x‖*‖y‖)*‖v i‖^2 := by ring

theorem sqrt_quadratic {T : E →L[ℂ] E} (hp : T.IsPositive) (x : E) :
    (inner ℂ x (T x)).re = ‖positiveRoot T x‖^2 := by
  change (inner ℂ x (T x)).re = ‖CFC.sqrt T x‖^2
  have hn : 0 ≤ T := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hp
  have hs (x y : E) : inner ℂ (CFC.sqrt T x) y = inner ℂ x (CFC.sqrt T y) :=
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg T)).isSymmetric x y
  have he : CFC.sqrt T (CFC.sqrt T x) = T x := by
    simpa [pow_two] using congrArg (fun A : E →L[ℂ] E => A x) (CFC.sq_sqrt T hn)
  rw [← he, ← hs]
  simp [← Complex.ofReal_pow]

theorem sqrt_ensemble (b : HilbertBasis I ℂ E) {T : E →L[ℂ] E}
    (hp : T.IsPositive) (ht : Summable (fun i => (inner ℂ (b i) (T (b i))).re)) :
    operator (fun i => positiveRoot T (b i)) = T := by
  have hv : Summable (fun i => ‖CFC.sqrt T (b i)‖^2) := by
    simpa only [sqrt_quadratic hp, positiveRoot] using ht
  have hn : 0 ≤ T := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hp
  have hs (x y : E) : inner ℂ (CFC.sqrt T x) y = inner ℂ x (CFC.sqrt T y) :=
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg T)).isSymmetric x y
  ext y
  apply ext_inner_left ℂ
  intro x
  have he : inner ℂ (CFC.sqrt T x) (CFC.sqrt T y) = inner ℂ x (T y) := by
    rw [hs]
    congr 1
    simpa [pow_two] using congrArg (fun A : E →L[ℂ] E => A y) (CFC.sq_sqrt T hn)
  have hh := b.hasSum_inner_mul_inner (CFC.sqrt T x) (CFC.sqrt T y)
  have hrow (i : I) : inner ℂ x (CFC.sqrt T (b i)) * inner ℂ (CFC.sqrt T (b i)) y =
      inner ℂ (CFC.sqrt T x) (b i) * inner ℂ (b i) (CFC.sqrt T y) := by
    rw [hs, hs]
  exact (hasSum_entry hv x y).unique (by simpa only [← hrow, he] using hh)

end TraceEnsemble

namespace EntropyPhotonNumber

def channelNumberBasis (n : ℕ) : HilbertBasis (NumberIndex n) ℂ (Fock n) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

@[simp] theorem channelNumberBasis_apply {n : ℕ} (a : NumberIndex n) :
    channelNumberBasis n a = numberKet a := by
  exact ((channelNumberBasis n).repr_symm_single a).symm

def rootColumn {n : ℕ} (ρ : State n) (a : NumberIndex n) : Fock n :=
  TraceEnsemble.positiveRoot ρ.op (numberKet a)

theorem rootColumn_norm {n : ℕ} (ρ : State n) :
    HasSum (fun a => ‖rootColumn ρ a‖^2) 1 := by
  have h := ρ.trace_one
  simp only [entry, TraceEnsemble.sqrt_quadratic ρ.positive] at h
  exact h

theorem rootColumn_operator {n : ℕ} (ρ : State n) :
    TraceEnsemble.operator (rootColumn ρ) = ρ.op := by
  have ht : Summable (fun a => (inner ℂ (channelNumberBasis n a)
      (ρ.op (channelNumberBasis n a))).re) := by
    simpa only [channelNumberBasis_apply, entry] using ρ.trace_one.summable
  have h := TraceEnsemble.sqrt_ensemble (T := ρ.op) (channelNumberBasis n) ρ.positive ht
  simp only [channelNumberBasis_apply] at h
  convert h using 1

def numberMoment {n : ℕ} (m : ℕ) (ρ : State n) : ℝ :=
  ∑' k, (1+(totalNumber k : ℝ))^m * (entry ρ.op k k).re

def FiniteMoment {n : ℕ} (m : ℕ) (ρ : State n) : Prop :=
  Summable (fun k => (1+(totalNumber k : ℝ))^m * (entry ρ.op k k).re)

end EntropyPhotonNumber

namespace WeightedShift
open scoped BigOperators ComplexConjugate
variable {I K : Type*} [DecidableEq K]

theorem weighted_entries_summable (w : K → ℝ) (v : I → H K)
    (hv : Summable (fun i => ‖v i‖^2))
    (hm : Summable (fun k => w k^2 * (inner ℂ (lp.single 2 k 1)
      (TraceEnsemble.operator v (lp.single 2 k 1))).re)) :
    Summable (fun z : I × K => ‖((w z.2 : ℂ)*v z.1 z.2)‖^2) := by
  have hr (k : K) : HasSum (fun i => w k^2*‖v i k‖^2)
      (w k^2 * (inner ℂ (lp.single 2 k 1)
        (TraceEnsemble.operator v (lp.single 2 k 1))).re) := by
    have hh := (TraceEnsemble.hasSum_quadratic hv (lp.single 2 k 1)).mul_left (w k^2)
    simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using hh
  have hs : Summable (fun z : K × I => w z.1^2*‖v z.2 z.1‖^2) :=
    (summable_prod_of_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))).mpr
      ⟨fun k => (hr k).summable, hm.congr (fun k => (hr k).tsum_eq.symm)⟩
  convert hs.prod_symm using 1
  funext z
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rfl

def weightedFamily (w : K → ℝ) (v : I → H K)
    (hs : Summable (fun z : I × K => ‖((w z.2 : ℂ)*v z.1 z.2)‖^2)) (i : I) : H K :=
  ⟨fun k => (w k : ℂ)*v i k,
    (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        ((summable_prod_of_nonneg (fun z : I × K => sq_nonneg
          ‖((w z.2 : ℂ)*v z.1 z.2)‖)).mp hs).1 i)⟩

omit [DecidableEq K] in
@[simp] theorem weightedFamily_apply (w : K → ℝ) (v : I → H K)
    (hs : Summable (fun z : I × K => ‖((w z.2 : ℂ)*v z.1 z.2)‖^2)) (i : I) (k : K) :
    weightedFamily w v hs i k=(w k:ℂ)*v i k := rfl

omit [DecidableEq K] in
theorem weightedFamily_summable (w : K → ℝ) (v : I → H K)
    (hs : Summable (fun z : I × K => ‖((w z.2 : ℂ)*v z.1 z.2)‖^2)) :
    Summable (fun i => ‖weightedFamily w v hs i‖^2) := by
  have ht := ((summable_prod_of_nonneg (fun z : I × K => sq_nonneg
    ‖((w z.2 : ℂ)*v z.1 z.2)‖)).mp hs).2
  apply ht.congr
  intro i
  exact (hasSum_square (weightedFamily w v hs i)).tsum_eq
end WeightedShift

namespace EntropyPhotonNumber
open QuantumTrace WeightedShift Annihilation
variable {n : ℕ}

theorem root_weighted_entries (m : ℕ) (ρ : State n) (hm : FiniteMoment (2*m) ρ) :
    Summable (fun z : NumberIndex n × NumberIndex n =>
      ‖((numberWeight z.2^m : ℝ):ℂ)*rootColumn ρ z.1 z.2‖^2) := by
  apply weighted_entries_summable (fun k => numberWeight k^m) (rootColumn ρ)
    (rootColumn_norm ρ).summable
  simpa only [rootColumn_operator, ← pow_mul, mul_comm m 2, numberWeight,
    totalNumber, Nat.cast_sum, entry, numberKet, FiniteMoment] using hm

def weightedRoot (m : ℕ) (ρ : State n) (hm : FiniteMoment (2*m) ρ) :
    NumberIndex n → Fock n :=
  weightedFamily (fun k => numberWeight k^m) (rootColumn ρ) (root_weighted_entries m ρ hm)

@[simp] theorem weightedRoot_apply (m : ℕ) (ρ : State n) (hm : FiniteMoment (2*m) ρ)
    (i k : NumberIndex n) : weightedRoot m ρ hm i k=((numberWeight k^m:ℝ):ℂ)*rootColumn ρ i k := rfl

theorem weightedRoot_summable (m : ℕ) (ρ : State n) (hm : FiniteMoment (2*m) ρ) :
    Summable (fun i => ‖weightedRoot m ρ hm i‖^2) :=
  weightedFamily_summable _ _ _

theorem inverse_weightedRoot (m : ℕ) (ρ : State n) (hm : FiniteMoment (2*m) ρ)
    (i : NumberIndex n) : inverseWeight m (weightedRoot m ρ hm i)=rootColumn ρ i := by
  apply lp.ext
  funext k
  simp only [inverseWeight_apply, weightedRoot_apply, Complex.ofReal_pow]
  have hw : (numberWeight k:ℂ) ≠ 0 := by
    exact_mod_cast (show numberWeight k ≠ 0 by linarith [numberWeight_one_le k])
  field_simp
end EntropyPhotonNumber

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end WeightedGenerator

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation
variable {n : ℕ} {J : Type*}

end EntropyPhotonNumber

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def eigenEnsemble (b : HilbertBasis J ℂ E) (p : J → ℝ) (j : J) : E :=
  (Real.sqrt (p j) : ℂ) • b j

omit [CompleteSpace E] in
theorem eigenEnsemble_norm (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (j : J) : ‖eigenEnsemble b p j‖^2=p j := by
  simp only [eigenEnsemble, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    b.orthonormal.norm_eq_one j, mul_one, sq_abs, Real.sq_sqrt (hp j)]

theorem eigenEnsemble_operator (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hs : Summable p) (T : E →L[ℂ] E) (hT : T.IsSymmetric)
    (he : ∀ j, T (b j)=(p j : ℂ) • b j) :
    operator (eigenEnsemble b p) (eigenEnsemble b p)=T := by
  have hn : Summable (fun j => ‖eigenEnsemble b p j‖^2) := by
    simpa only [eigenEnsemble_norm b p hp] using hs
  ext y
  apply ext_inner_left ℂ
  intro x
  have hprod (j : J) : inner ℂ x (eigenEnsemble b p j)*inner ℂ (eigenEnsemble b p j) y =
      inner ℂ x (b j)*inner ℂ (b j) (T y) := by
    have hsym := hT (b j) y
    change inner ℂ (T (b j)) y = inner ℂ (b j) (T y) at hsym
    rw [← hsym, he]
    simp only [eigenEnsemble, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    calc
      _ = ((Real.sqrt (p j) : ℂ)^2)*(inner ℂ x (b j)*inner ℂ (b j) y) := by ring
      _ = _ := by rw [← Complex.ofReal_pow, Real.sq_sqrt (hp j)]; ring
  exact (entry_hasSum hn hn x y).unique (by simpa only [hprod] using b.hasSum_inner_mul_inner x (T y))
end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
variable {n : ℕ} {I J K : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber
open Annihilation CrossEnsemble
variable {n : ℕ} {J : Type*}

end EntropyPhotonNumber

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped ComplexConjugate
variable {n : ℕ}

theorem log_mode_left (S : Fock n →L[ℂ] Fock n) (hS : S.IsSymmetric)
    (x : Fock n) (c : ℝ)
    (he : S (inverseWeight 1 x) = (c : ℂ) • inverseWeight 5 x)
    (j : Fin n) (u : Bool) :
    inner ℂ (inverseWeight 1 x) (S (modeBound j u x)) =
      ((c*‖unweightedGain j u (inverseWeight 2 x)‖^2 : ℝ) : ℂ) := by
  have hsym := hS (inverseWeight 1 x) (modeBound j u x)
  change inner ℂ (S (inverseWeight 1 x)) (modeBound j u x) =
    inner ℂ (inverseWeight 1 x) (S (modeBound j u x)) at hsym
  rw [← hsym, he, inner_smul_left, Complex.conj_ofReal, Complex.ofReal_mul]
  congr 1
  calc
    _ = inner ℂ (inverseWeight 3 x) (inverseWeight 2 (modeBound j u x)) := by
      rw [show inverseWeight 5 x = inverseWeight 2 (inverseWeight 3 x) from
        congrArg (fun T : Fock n →L[ℂ] Fock n => T x) (inverseWeight_add 2 3)]
      exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (inverseWeight_selfAdjoint 2) _ _
    _ = _ := mode_quadratic j u x

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {J : Type*}

def spectralGain (b : HilbertBasis J ℂ (Fock n)) (x : J → Fock n)
    (j : Fin n) (u : Bool) (l r : J) : ℂ :=
  inner ℂ (b l) (unweightedGain j u (inverseWeight 2 (x r)))

theorem crossed_log_summable (b : HilbertBasis J ℂ (Fock n))
    (x : J → Fock n) (hx : Summable (fun r => ‖x r‖^2))
    (S : Fock n →L[ℂ] Fock n) (c : J → ℝ) (hc : ∀ l, 0 ≤ c l)
    (hf : ∀ y, HasSum (fun l => c l*‖inner ℂ (b l) (inverseWeight 2 y)‖^2)
      (inner ℂ y (S y)).re) (j : Fin n) (u : Bool) :
    Summable (fun a : J × J => c a.1*‖spectralGain b x j u a.1 a.2‖^2) := by
  have hcol (r : J) : HasSum (fun l => c l*‖spectralGain b x j u l r‖^2)
      (inner ℂ (gain j u (x r)) (S (gain j u (x r)))).re := by
    have he := congrArg (fun T : Fock n →L[ℂ] Fock n => T (x r)) (gain_factor j u)
    change inverseWeight 2 (gain j u (x r)) = unweightedGain j u (inverseWeight 2 (x r)) at he
    simpa only [he, spectralGain] using hf (gain j u (x r))
  have ha := CrossEnsemble.applied_summable hx (gain j u)
  have hs : Summable (fun r => (inner ℂ (gain j u (x r)) (S (gain j u (x r)))).re) :=
    ((CrossEnsemble.pairing_summable ha ha S).hasSum.mapL Complex.reCLM).summable
  suffices hs : Summable (fun a : J × J => c a.2*‖spectralGain b x j u a.2 a.1‖^2) from hs.prod_symm
  apply (summable_prod_of_nonneg (fun a : J × J => mul_nonneg (hc a.2) (sq_nonneg _))).mpr
  refine ⟨fun r => (hcol r).summable, ?_⟩
  simpa only [(hcol _).tsum_eq] using hs

theorem uncrossed_log_summable (b : HilbertBasis J ℂ (Fock n))
    (x : J → Fock n) (hx : Summable (fun r => ‖x r‖^2))
    (S : Fock n →L[ℂ] Fock n) (hS : S.IsSymmetric) (c : J → ℝ)
    (hc : ∀ l, 0 ≤ c l)
    (he : ∀ r, S (inverseWeight 1 (x r)) = (c r : ℂ) • inverseWeight 5 (x r))
    (j : Fin n) (u : Bool) :
    Summable (fun a : J × J => c a.2*‖spectralGain b x j u a.1 a.2‖^2) := by
  have hcol (r : J) : HasSum (fun l => c r*‖spectralGain b x j u l r‖^2)
      (c r*‖unweightedGain j u (inverseWeight 2 (x r))‖^2) := by
    exact (TraceEnsemble.basis_hasSum_norm_sq b _).mul_left _
  have ha := CrossEnsemble.applied_summable hx (modeBound j u)
  have hv := CrossEnsemble.applied_summable hx (inverseWeight 1)
  have hs := ((CrossEnsemble.pairing_summable ha hv S).hasSum.mapL Complex.reCLM).summable
  simp only [Complex.reCLM_apply, log_mode_left S hS _ _ (he _) j u, Complex.ofReal_re] at hs
  suffices hs : Summable (fun a : J × J => c a.1*‖spectralGain b x j u a.2 a.1‖^2) from hs.prod_symm
  apply (summable_prod_of_nonneg (fun a : J × J => mul_nonneg (hc a.1) (sq_nonneg _))).mpr
  refine ⟨fun r => (hcol r).summable, ?_⟩
  simpa only [(hcol _).tsum_eq] using hs

end WeightedGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation

structure GibbsData (n : ℕ) (k : ℝ) (ρ : State n) where
  B : Fock n →L[ℂ] Fock n
  positive : B.IsPositive
  J : Type
  nonempty : Nonempty J
  basis : HilbertBasis J ℂ (Fock n)
  eigenval : J → ℝ
  positive_eigenval : ∀ j, 0 < eigenval j
  heat : Summable (fun j => Real.exp (-eigenval j))
  inverse_eigen : ∀ j, gibbsInverse rootNumberWeight rootNumberWeight_one_le k B (basis j) =
    (((eigenval j)⁻¹ : ℝ) : ℂ) • basis j
  operator_eq : ρ.op = spectralGibbs basis eigenval heat
  faithful : Function.Injective ρ.op
  moment : FiniteMoment 7 ρ

variable {n : ℕ} {k : ℝ} {ρ : State n}

theorem inversePower_root_four :
    inversePower (rootNumberWeight (n := n)) rootNumberWeight_one_le 4 = inverseWeight 2 := by
  ext y i
  simp only [inversePower_apply, rootNumberWeight_pow_four, inverseWeight_apply,
    Complex.ofReal_inv, Complex.ofReal_pow]

theorem finiteMoment_mono {m l : ℕ} (hml : m ≤ l) (hρ : FiniteMoment l ρ) :
    FiniteMoment m ρ := by
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (by positivity) (ρ.positive.re_inner_nonneg_right _)) _ hρ
  intro i
  apply mul_le_mul_of_nonneg_right _ (ρ.positive.re_inner_nonneg_right _)
  exact pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) (totalNumber i)] : (1:ℝ) ≤ 1+↑(totalNumber i)) hml

namespace GibbsData
variable (G : GibbsData n k ρ)

def logSandwich : Fock n →L[ℂ] Fock n :=
  logarithmSandwich (gibbsFactor (rootNumberWeight (n := n)) rootNumberWeight_one_le k G.B)
    (inverseWeight 2) (Real.log (heatPartition G.eigenval))

def probability (j : G.J) : ℝ := gibbsWeight G.eigenval j

def logCoefficient (j : G.J) : ℝ := -Real.log (G.probability j)

theorem probability_pos (j : G.J) : 0 < G.probability j := by
  let : Nonempty G.J := G.nonempty
  exact gibbsWeight_pos G.eigenval G.heat j

theorem probability_sum : HasSum G.probability 1 := by
  let : Nonempty G.J := G.nonempty
  exact gibbsWeight_hasSum G.eigenval G.heat

theorem logCoefficient_nonneg (j : G.J) : 0 ≤ G.logCoefficient j := by
  apply neg_nonneg.mpr
  apply Real.log_nonpos (G.probability_pos j).le
  have hh := G.probability_sum.summable.le_tsum j (fun i _ => (G.probability_pos i).le)
  rwa [G.probability_sum.tsum_eq] at hh

theorem eigen (j : G.J) : ρ.op (G.basis j)=(G.probability j : ℂ) • G.basis j := by
  let : Nonempty G.J := G.nonempty
  rw [G.operator_eq]
  exact spectralGibbs_eigen G.basis G.eigenval G.heat j

theorem logSandwich_symmetric (hk : 0 < k) : G.logSandwich.IsSymmetric := by
  have hA := (ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (gibbsFactor_strictPositive rootNumberWeight rootNumberWeight_one_le hk G.positive).nonneg
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
  unfold logSandwich logarithmSandwich
  apply IsSelfAdjoint.add hA.isSelfAdjoint
  have hs : IsSelfAdjoint ((inverseWeight (n := n) 2)*(inverseWeight 2)) :=
    by simpa only [pow_two] using (inverseWeight_selfAdjoint (n := n) 2).pow 2
  exact (show IsSelfAdjoint (Real.log (heatPartition G.eigenval) : ℂ) from Complex.conj_ofReal _).smul hs

theorem logSandwich_parseval (hk : 0 < k) (y : Fock n) :
    HasSum (fun j => G.logCoefficient j*‖inner ℂ (G.basis j) (inverseWeight 2 y)‖^2)
      (inner ℂ y (G.logSandwich y)).re := by
  let : Nonempty G.J := G.nonempty
  have he (j : G.J) : ((inverseWeight (n := n) 2) *
      Ring.inverse (gibbsFactor (rootNumberWeight (n := n)) rootNumberWeight_one_le k G.B)*
      inverseWeight 2 : Fock n →L[ℂ] Fock n) (G.basis j)=(((G.eigenval j)⁻¹ : ℝ):ℂ) • G.basis j := by
    simpa only [gibbsInverse, inversePower_root_four] using G.inverse_eigen j
  exact gibbs_logarithmSandwich_parseval G.basis _ _
    (gibbsFactor_strictPositive _ _ hk G.positive)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (inverseWeight_selfAdjoint 2))
    (inverseWeight_injective 2) G.eigenval G.positive_eigenval he G.heat y

theorem logSandwich_preimage (hk : 0 < k) (j : G.J) (x : Fock n)
    (hi : inverseWeight 3 x = CrossEnsemble.eigenEnsemble G.basis G.probability j) :
    G.logSandwich (inverseWeight 1 x) =
      (G.logCoefficient j : ℂ) • inverseWeight 5 x := by
  let : Nonempty G.J := G.nonempty
  have he (j : G.J) : ((inverseWeight (n := n) 2) *
      Ring.inverse (gibbsFactor (rootNumberWeight (n := n)) rootNumberWeight_one_le k G.B)*
      inverseWeight 2 : Fock n →L[ℂ] Fock n) (G.basis j)=(((G.eigenval j)⁻¹ : ℝ):ℂ) • G.basis j := by
    simpa only [gibbsInverse, inversePower_root_four] using G.inverse_eigen j
  have hv : inverseWeight 2 (inverseWeight 1 x)=
      (Real.sqrt (G.probability j):ℂ) • G.basis j := by
    change (inverseWeight 2 ∘L inverseWeight 1) x = _
    rw [← inverseWeight_add]
    exact hi
  have hh := logarithmSandwich_eigen_preimage G.basis _ _
    (gibbsFactor_strictPositive _ _ hk G.positive) (inverseWeight_injective 2)
    G.eigenval G.positive_eigenval he (Real.log (heatPartition G.eigenval)) j
    (inverseWeight 1 x) (Real.sqrt (G.probability j):ℂ) hv
  have hc : G.eigenval j+Real.log (heatPartition G.eigenval)=G.logCoefficient j := by
    simp only [logCoefficient, probability, log_gibbsWeight G.eigenval G.heat]
  have hid : inverseWeight 2 ((Real.sqrt (G.probability j):ℂ) • G.basis j)=inverseWeight 5 x := by
    rw [← hv]
    change (inverseWeight 2 ∘L inverseWeight 2 ∘L inverseWeight 1) x= inverseWeight 5 x
    rw [← inverseWeight_add, ← inverseWeight_add]
  exact (hh.trans (by rw [hc, hid]))

theorem weighted_columns : ∃ x : G.J → Fock n,
    Summable (fun j => ‖x j‖^2) ∧
    (∀ j, inverseWeight 3 (x j)=CrossEnsemble.eigenEnsemble G.basis G.probability j) := by
  have hm6 := finiteMoment_mono (by norm_num : 6 ≤ 7) G.moment
  have hm : Summable (fun i => (numberWeight i^3)^2*
      (inner ℂ (sequenceBasis (NumberIndex n) i) (ρ.op (sequenceBasis _ i))).re) := by
    have hb (i : NumberIndex n) : sequenceBasis (NumberIndex n) i = numberKet i := by
      ext a
      by_cases ha : i=a <;> simp [sequenceBasis_apply, numberKet, ha]
    simpa only [← pow_mul, show (3*2:ℕ)=6 from rfl, numberWeight, totalNumber, Nat.cast_sum,
      FiniteMoment, entry, hb] using hm6
  obtain ⟨x, hx, hs, _⟩ := weighted_spectral_vectors G.basis ρ.op G.probability
    (fun j => (G.probability_pos j).le) G.eigen (fun i => numberWeight i^3) hm
  refine ⟨x, hs, fun j => ?_⟩
  apply lp.ext
  funext i
  simp only [inverseWeight_apply, hx, CrossEnsemble.eigenEnsemble, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, Complex.ofReal_pow]
  have hw : (numberWeight i : ℂ) ≠ 0 := by
    exact_mod_cast (show numberWeight i ≠ 0 by linarith [numberWeight_one_le i])
  field_simp

end GibbsData
end EntropyPhotonNumber

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
variable {n : ℕ} {J : Type*}

def loweringEntry (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (x : J → Fock n) (j : Fin n) (l r : J) : ℂ :=
  spectralGain b x j false l r / (Real.sqrt (p r) : ℂ)

theorem spectralGain_adjoint (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (x : J → Fock n)
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (j : Fin n) (l r : J) :
    (Real.sqrt (p l):ℂ)*spectralGain b x j true l r =
      (Real.sqrt (p r):ℂ)*conj (spectralGain b x j false r l) := by
  have h := ladder_adjoint_pairing j (inverseWeight 2 (x l)) (inverseWeight 2 (x r))
  have hw (r : J) : inverseWeight 1 (inverseWeight 2 (x r))=(Real.sqrt (p r):ℂ) • b r := by
    change (inverseWeight 1 ∘L inverseWeight 2) (x r)=_
    rw [← inverseWeight_add]
    exact hi r
  rw [hw l, hw r, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  simpa only [spectralGain, unweightedGain, Bool.false_eq_true, ↓reduceIte,
    inner_conj_symm, mul_comm] using h.symm

theorem spectralGain_lowering (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n) (j : Fin n) (l r : J) :
    spectralGain b x j false l r=(Real.sqrt (p r):ℂ)*loweringEntry b p x j l r := by
  unfold loweringEntry
  have h : (Real.sqrt (p r):ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (hp r)).ne'
  field_simp

theorem spectralGain_raising (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (j : Fin n) (l r : J) :
    spectralGain b x j true r l=(Real.sqrt (p l):ℂ)*conj (loweringEntry b p x j l r) := by
  have he := spectralGain_adjoint b p x hi j r l
  rw [spectralGain_lowering b p hp x j l r, map_mul, Complex.conj_ofReal] at he
  have hn : (Real.sqrt (p r):ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (hp r)).ne'
  apply mul_left_cancel₀ hn
  linear_combination he

theorem spectralGain_lowering_sq (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n) (j : Fin n) (l r : J) :
    ‖spectralGain b x j false l r‖^2=p r*‖loweringEntry b p x j l r‖^2 := by
  rw [spectralGain_lowering b p hp, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hp r).le]

theorem spectralGain_raising_sq (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (j : Fin n) (l r : J) :
    ‖spectralGain b x j true r l‖^2=p l*‖loweringEntry b p x j l r‖^2 := by
  rw [spectralGain_raising b p hp x hi, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hp l).le,
    Complex.norm_conj]

end WeightedGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation
variable {n : ℕ} {k : ℝ} {ρ : State n}
namespace GibbsData
variable (G : GibbsData n k ρ)

def spectralColumns : G.J → Fock n := Classical.choose G.weighted_columns

theorem spectralColumns_summable : Summable (fun r => ‖G.spectralColumns r‖^2) :=
  (Classical.choose_spec G.weighted_columns).1

theorem spectralColumns_inverse (r : G.J) :
    inverseWeight 3 (G.spectralColumns r)=CrossEnsemble.eigenEnsemble G.basis G.probability r :=
  (Classical.choose_spec G.weighted_columns).2 r

end GibbsData
end EntropyPhotonNumber

end

end OAI
