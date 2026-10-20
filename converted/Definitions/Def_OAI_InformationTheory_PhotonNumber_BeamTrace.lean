/-
prove2.me platform library module `Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_InformationTheory_PhotonNumber_BeamTrace.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/BeamTrace.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntropyPhotonNumber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Prove2me.Shim.Misc  -- conversion shim (platform Mathlib API)

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}
end Annihilation

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}
def W (ke : NumberIndex n × NumberIndex n) : ℝ := numberWeight ke.1+numberWeight ke.2-1

theorem W_one_le (ke : NumberIndex n × NumberIndex n) : 1 ≤ W ke := by
  dsimp [W]
  linarith [numberWeight_one_le ke.1, numberWeight_one_le ke.2]

def upL (j : Fin n) (ke : NumberIndex n × NumberIndex n) := (up j ke.1,ke.2)
def upR (j : Fin n) (ke : NumberIndex n × NumberIndex n) := (ke.1,up j ke.2)

theorem upL_inj (j : Fin n) : Function.Injective (upL j) := by
  intro x y h
  change (up j x.1,x.2)=(up j y.1,y.2) at h
  exact Prod.ext (up_injective j (Prod.mk.inj h).1) (Prod.mk.inj h).2
theorem upR_inj (j : Fin n) : Function.Injective (upR j) := by
  intro x y h
  change (x.1,up j x.2)=(y.1,up j y.2) at h
  exact Prod.ext (Prod.mk.inj h).1 (up_injective j (Prod.mk.inj h).2)
@[simp] theorem W_upL (j : Fin n) (ke : NumberIndex n × NumberIndex n) : W (upL j ke)=W ke+1 := by
  simp only [W, upL, weight_up]
  ring
@[simp] theorem W_upR (j : Fin n) (ke : NumberIndex n × NumberIndex n) : W (upR j ke)=W ke+1 := by
  simp only [W, upR, weight_up]
  ring

theorem coordinate_le (j : Fin n) (k : NumberIndex n) : (k j:ℝ)+1 ≤ numberWeight k := by
  unfold numberWeight
  have hh : (k j:ℝ) ≤ ∑ i : Fin n, (k i:ℝ) := Finset.single_le_sum (fun (i : Fin n) (_hi : i ∈ Finset.univ) => Nat.cast_nonneg (k i)) (Finset.mem_univ j)
  linarith

theorem lowerL_bound (j : Fin n) (ke : NumberIndex n × NumberIndex n) :
    ‖((Real.sqrt ((ke.1 j:ℝ)+1)/(W ke+1):ℝ):ℂ)‖ ≤ 1 := by
  have hw : 0 < W ke+1 := by linarith [W_one_le ke]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hw.le)]
  apply (div_le_one (by linarith [W_one_le ke])).mpr
  have hs : Real.sqrt ((ke.1 j:ℝ)+1) ≤ (ke.1 j:ℝ)+1 := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith [Nat.cast_nonneg (ke.1 j) (α:=ℝ)]))
  dsimp [W]
  linarith [coordinate_le j ke.1, numberWeight_one_le ke.2]

theorem lowerR_bound (j : Fin n) (ke : NumberIndex n × NumberIndex n) :
    ‖((Real.sqrt ((ke.2 j:ℝ)+1)/(W ke+1):ℝ):ℂ)‖ ≤ 1 := by
  have hw : 0 < W ke+1 := by linarith [W_one_le ke]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hw.le)]
  apply (div_le_one (by linarith [W_one_le ke])).mpr
  have hs : Real.sqrt ((ke.2 j:ℝ)+1) ≤ (ke.2 j:ℝ)+1 := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith [Nat.cast_nonneg (ke.2 j) (α:=ℝ)]))
  dsimp [W]
  linarith [coordinate_le j ke.2, numberWeight_one_le ke.1]

def lowerL (j : Fin n) : JointFock n →L[ℂ] JointFock n :=
  WeightedShift.pullCLM (upL j) (upL_inj j)
    (fun ke => ((Real.sqrt ((ke.1 j:ℝ)+1)/(W ke+1):ℝ):ℂ)) 1 (by norm_num) (lowerL_bound j)
def lowerR (j : Fin n) : JointFock n →L[ℂ] JointFock n :=
  WeightedShift.pullCLM (upR j) (upR_inj j)
    (fun ke => ((Real.sqrt ((ke.2 j:ℝ)+1)/(W ke+1):ℝ):ℂ)) 1 (by norm_num) (lowerR_bound j)
@[simp] theorem lowerL_apply (j : Fin n) (x : JointFock n) (ke : NumberIndex n × NumberIndex n) :
    lowerL j x ke=((Real.sqrt ((ke.1 j:ℝ)+1)/(W ke+1):ℝ):ℂ)*x (upL j ke) := rfl
@[simp] theorem lowerR_apply (j : Fin n) (x : JointFock n) (ke : NumberIndex n × NumberIndex n) :
    lowerR j x ke=((Real.sqrt ((ke.2 j:ℝ)+1)/(W ke+1):ℝ):ℂ)*x (upR j ke) := rfl

end BeamLadder

namespace EntropyPhotonNumber
end EntropyPhotonNumber

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

def radial (f : ℝ → ℝ) (C : ℝ) (hC : 0≤C) (hf : ∀ ke : NumberIndex n × NumberIndex n, |f (W ke)|≤C) :
    JointFock n →L[ℂ] JointFock n :=
  WeightedShift.pullCLM id Function.injective_id (fun ke => (f (W ke):ℂ)) C hC
    (fun ke => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hf ke)

@[simp] theorem radial_apply (f : ℝ → ℝ) (C : ℝ) (hC : 0≤C)
    (hf : ∀ ke : NumberIndex n × NumberIndex n, |f (W ke)|≤C)
    (x : JointFock n) (ke : NumberIndex n × NumberIndex n) :
    radial f C hC hf x ke=(f (W ke):ℂ)*x ke := rfl

end

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}

def increase (w : ℝ) : ℝ := if 1<w then w/(w-1) else 0

theorem W_nat (ke : NumberIndex n × NumberIndex n) :
    W ke = ((∑j, ke.1 j)+(∑j, ke.2 j):ℕ)+1 := by
  simp only [W, numberWeight, Nat.cast_add, Nat.cast_sum]
  ring

theorem increase_bound (ke : NumberIndex n × NumberIndex n) : |increase (W ke)|≤2 := by
  unfold increase
  split_ifs with hh
  · have hh₂ : 2≤W ke := by
      rw [W_nat] at hh ⊢
      have hn : 1≤(∑j, ke.1 j)+(∑j, ke.2 j) := by exact_mod_cast (by linarith : (0:ℝ)<(((∑j, ke.1 j)+(∑j, ke.2 j):ℕ):ℝ))
      exact_mod_cast Nat.succ_le_succ hn
    rw [abs_of_nonneg (div_nonneg (by linarith) (by linarith))]
    apply (div_le_iff₀ (by linarith : 0<W ke-1)).mpr
    linarith
  · norm_num

def raiseL (j : Fin n) : JointFock n →L[ℂ] JointFock n :=
  radial increase 2 (by norm_num) increase_bound ∘L (lowerL j).adjoint

def raiseR (j : Fin n) : JointFock n →L[ℂ] JointFock n :=
  radial increase 2 (by norm_num) increase_bound ∘L (lowerR j).adjoint

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

theorem inverse_bound (ke : NumberIndex n × NumberIndex n) : |(W ke)⁻¹|≤1 := by
  rw [abs_of_nonneg (inv_nonneg.mpr (by linarith [W_one_le ke]))]
  exact inv_le_one_of_one_le₀ (W_one_le ke)

def inverse : JointFock n →L[ℂ] JointFock n :=
  radial (fun t => t⁻¹) 1 (by norm_num) inverse_bound

@[simp] theorem inverse_apply (x : JointFock n) (ke : NumberIndex n × NumberIndex n) :
    inverse x ke=((W ke)⁻¹:ℂ)*x ke := by
  change (((W ke)⁻¹:ℝ):ℂ)*x ke=_
  rw [Complex.ofReal_inv]

def conjugate (η : ℝ) (hη : η ∈ Set.Icc 0 1) (Z : Fock n →L[ℂ] Fock n) :
    JointFock n →L[ℂ] JointFock n :=
  (beamUnitary η hη).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    liftLeft Z ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap

def weakL (r : ℝ) (j : Fin n) (x y : JointFock n)
    (T : JointFock n →L[ℂ] JointFock n) : ℂ :=
  (r+1:ℂ)*inner ℂ (lowerL j x) (T (inverse y))-
    (r:ℂ)*inner ℂ (inverse x) (T (raiseL j y))

def weakR (r : ℝ) (j : Fin n) (x y : JointFock n)
    (T : JointFock n →L[ℂ] JointFock n) : ℂ :=
  (r+1:ℂ)*inner ℂ (lowerR j x) (T (inverse y))-
    (r:ℂ)*inner ℂ (inverse x) (T (raiseR j y))

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

def tensorPreimage (x y : Fock n) : JointFock n :=
  tensor (inverseWeight 2 x) (inverseWeight 3 y)+
    tensor (inverseWeight 3 x) (inverseWeight 2 y)-
    tensor (inverseWeight 3 x) (inverseWeight 3 y)

end BeamLadder

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap

namespace KrausBounded

section
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def wave (V : I → E →L[ℂ] H) (hs : ∀ x, Summable (fun i => ‖V i x‖^2)) (x : E) :
    lp (fun _ : I => H) 2 :=
  ⟨fun i => V i x, (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
    (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs x)⟩

@[simp] theorem wave_apply (V : I → E →L[ℂ] H) (hs : ∀ x, Summable (fun i => ‖V i x‖^2))
    (x : E) (i : I) : wave V hs x i = V i x := rfl

 theorem wave_square (V : I → E →L[ℂ] H) (hs : ∀ x, Summable (fun i => ‖V i x‖^2)) (x : E) :
    ‖wave V hs x‖^2 = ∑' i, ‖V i x‖^2 := by
  symm
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, wave_apply] using
    (lp.hasSum_norm (p := 2) (by norm_num) (wave V hs x)).tsum_eq

def linearMap (V : I → E →L[ℂ] H) (hs : ∀ x, Summable (fun i => ‖V i x‖^2)) :
    E →ₗ[ℂ] lp (fun _ : I => H) 2 where
  toFun := wave V hs
  map_add' := fun x y => by apply lp.ext; funext i; exact map_add (V i) x y
  map_smul' := fun c x => by apply lp.ext; funext i; exact map_smul (V i) c x

 theorem wave_bound (V : I → E →L[ℂ] H) (hs : ∀ x, Summable (fun i => ‖V i x‖^2))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖V i x‖^2) ≤ C^2*‖x‖^2) (x : E) :
    ‖wave V hs x‖ ≤ C*‖x‖ := by
  have hh := hb x
  rw [← wave_square V hs x] at hh
  nlinarith [norm_nonneg (wave V hs x), mul_nonneg hC (norm_nonneg x)]

def lift (V : I → E →L[ℂ] H) (hs : ∀ x, Summable (fun i => ‖V i x‖^2))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖V i x‖^2) ≤ C^2*‖x‖^2) :
    E →L[ℂ] lp (fun _ : I => H) 2 :=
  (linearMap V hs).mkContinuous C (wave_bound V hs hC hb)

 theorem sum_bound {V : I → E →L[ℂ] H} (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Z : H →L[ℂ] H) (x : E) :
    Summable (fun i => ‖Z (V i x)‖^2) ∧ (∑' i, ‖Z (V i x)‖^2) ≤ ‖Z‖^2*‖x‖^2 := by
  have hb (i : I) : ‖Z (V i x)‖^2 ≤ ‖Z‖^2*‖V i x‖^2 := by
    nlinarith [Z.le_opNorm (V i x), norm_nonneg (Z (V i x)), mul_nonneg (norm_nonneg Z) (norm_nonneg (V i x))]
  have hs := (hV x).summable.mul_left (‖Z‖^2)
  have ht := hs.of_nonneg_of_le (fun _ => sq_nonneg _) hb
  exact ⟨ht, (ht.tsum_le_tsum hb hs).trans_eq (by rw [tsum_mul_left, (hV x).tsum_eq])⟩

variable [CompleteSpace E] [CompleteSpace H]

def analysis (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2)) :
    E →L[ℂ] lp (fun _ : I => H) 2 :=
  lift V (fun x => (hV x).summable) 1 (by norm_num) (by intro x; simp [(hV x).tsum_eq])

def acted (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Z : H →L[ℂ] H) : E →L[ℂ] lp (fun _ : I => H) 2 :=
  lift (fun i => Z ∘L V i) (fun x => (sum_bound hV Z x).1) ‖Z‖ (norm_nonneg Z)
    (fun x => (sum_bound hV Z x).2)

def dual (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Z : H →L[ℂ] H) : E →L[ℂ] E := (analysis V hV).adjoint ∘L acted V hV Z

 theorem dual_entry (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Z : H →L[ℂ] H) (x y : E) :
    HasSum (fun i => inner ℂ (V i x) (Z (V i y))) (inner ℂ x (dual V hV Z y)) := by
  have hh := lp.hasSum_inner (𝕜 := ℂ) (analysis V hV x) (acted V hV Z y)
  rw [← ContinuousLinearMap.adjoint_inner_right] at hh
  exact hh

end

variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

 theorem dual_add (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Z T : H →L[ℂ] H) : dual V hV (Z+T) = dual V hV Z+dual V hV T := by
  ext y
  apply ext_inner_left ℂ
  intro x
  exact (dual_entry V hV (Z+T) x y).unique (by
    simpa only [add_apply, inner_add_right] using
      (dual_entry V hV Z x y).add (dual_entry V hV T x y))

 theorem dual_smul (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (c : ℂ) (Z : H →L[ℂ] H) : dual V hV (c • Z) = c • dual V hV Z := by
  ext y
  apply ext_inner_left ℂ
  intro x
  exact (dual_entry V hV (c • Z) x y).unique (by
    simpa only [smul_apply, inner_smul_right] using (dual_entry V hV Z x y).mul_left c)

end KrausBounded

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J : Type*}

 theorem rightFamily_norm (y : J → H B) (hy : HasSum (fun j => ‖y j‖^2) 1) (x : H A) :
    HasSum (fun j => ‖tensorRight (y j) x‖^2) (‖x‖^2) := by
  simpa only [tensorRight_apply, tensor_norm_sq, mul_one] using hy.mul_left (‖x‖^2)
 theorem leftFamily_norm (x : I → H A) (hx : HasSum (fun i => ‖x i‖^2) 1) (y : H B) :
    HasSum (fun i => ‖tensorLeft (x i) y‖^2) (‖y‖^2) := by
  simpa only [tensorLeft_apply, tensor_norm_sq, one_mul] using hx.mul_right (‖y‖^2)

def conditionalLeft (y : J → H B) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) : H A →L[ℂ] H A :=
  KrausBounded.dual (fun j => tensorRight (y j)) (rightFamily_norm y hy) Z

def conditionalRight (x : I → H A) (hx : HasSum (fun i => ‖x i‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) : H B →L[ℂ] H B :=
  KrausBounded.dual (fun i => tensorLeft (x i)) (leftFamily_norm x hx) Z

end TensorLp

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

def singleWeak (r : ℝ) (j : Fin n) (x : I → Fock n) (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  (r+1:ℂ)*CrossEnsemble.pairing (fun i => inverseWeight 3 (x i))
    (fun i => sandwich 0 3 (by omega) j (x i)) Z-
  (r:ℂ)*CrossEnsemble.pairing (fun i => creationSandwich 0 3 (by omega) j (x i))
    (fun i => inverseWeight 3 (x i)) Z

end BeamLadder

end

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal

namespace EntropyPhotonNumber
variable {n : ℕ}
theorem entry_ext {T R : Fock n →L[ℂ] Fock n}
    (h : ∀ k l, entry T k l = entry R k l) : T = R := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro l
  apply ContinuousLinearMap.ext
  intro c
  apply lp.ext
  funext k
  have h₁ : lp.single (E := fun _ : NumberIndex n => ℂ) 2 l c = c • numberKet l := by
    simp [numberKet, ← lp.single_smul]
  change T (lp.single 2 l c) k = R (lp.single 2 l c) k
  rw [h₁, map_smul, map_smul]
  have he := h k l
  simpa [entry, numberKet, lp.inner_single_left] using congrArg (fun z : ℂ => c*z) he
end EntropyPhotonNumber

namespace TensorLp
variable {A B I : Type*}
end TensorLp

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end CrossEnsemble

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace TensorLp
variable {A B I : Type*}

theorem hasSum_slice_family {v : I → H (A × B)} {t : ℝ}
    (hv : HasSum (fun i => ‖v i‖^2) t) :
    HasSum (fun bi : B × I => ‖slice (v bi.2) bi.1‖^2) t := by
  have hp (i : I) : (∑' b, ‖slice (v i) b‖^2) = ‖v i‖^2 := (hasSum_slice_norm_sq (v i)).tsum_eq
  have hd : Summable (fun ib : I × B => ‖slice (v ib.1) ib.2‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun i => (hasSum_slice_norm_sq (v i)).summable, ?_⟩
    simpa only [hp] using hv.summable
  have ht : (∑' ib : I × B, ‖slice (v ib.1) ib.2‖^2) = t := by
    rw [hd.tsum_prod]
    simpa only [hp] using hv.tsum_eq
  have hsum : HasSum (fun ib : I × B => ‖slice (v ib.1) ib.2‖^2) t := ht ▸ hd.hasSum
  exact (Equiv.prodComm B I).hasSum_iff.mpr hsum

def partialTrace (v : I → H (A × B)) : H A →L[ℂ] H A :=
  TraceEnsemble.operator (fun bi : B × I => slice (v bi.2) bi.1)

theorem partialTrace_positive {v : I → H (A × B)}
    (hv : Summable (fun i => ‖v i‖^2)) : (partialTrace v).IsPositive :=
  TraceEnsemble.positive (hasSum_slice_family hv.hasSum).summable

theorem partialTrace_trace {v : I → H (A × B)} {t : ℝ}
    (hv : HasSum (fun i => ‖v i‖^2) t) (b : HilbertBasis A ℂ (H A)) :
    HasSum (fun a => (inner ℂ (b a) (partialTrace v (b a))).re) t :=
  TraceEnsemble.trace (hasSum_slice_family hv) b

theorem partialTrace_entry [DecidableEq A] [DecidableEq B]
    {v : I → H (A × B)} (hv : Summable (fun i => ‖v i‖^2)) (a c : A) :
    HasSum (fun b => inner ℂ (lp.single 2 (a,b) 1)
      (TraceEnsemble.operator v (lp.single 2 (c,b) 1)))
      (inner ℂ (lp.single 2 a 1) (partialTrace v (lp.single 2 c 1))) := by
  have hs := TraceEnsemble.hasSum_entry (hasSum_slice_family hv.hasSum).summable
    (lp.single 2 a 1) (lp.single 2 c 1)
  have hrow (b : B) : HasSum
      (fun i => inner ℂ (lp.single 2 a 1) (slice (v i) b) *
        inner ℂ (slice (v i) b) (lp.single 2 c 1))
      (inner ℂ (lp.single 2 (a,b) 1) (TraceEnsemble.operator v (lp.single 2 (c,b) 1))) := by
    convert TraceEnsemble.hasSum_entry hv (lp.single 2 (a,b) 1) (lp.single 2 (c,b) 1) using 1
    ext i
    simp [lp.inner_single_left, lp.inner_single_right, slice_apply]
  exact hs.prod_fiberwise hrow

end TensorLp

namespace TraceEnsemble
open TensorLp
variable {A B I J : Type*}

theorem hasSum_tensor_norm {v : I → H A} {w : J → H B} {a b : ℝ}
    (hv : HasSum (fun i => ‖v i‖^2) a) (hw : HasSum (fun j => ‖w j‖^2) b) :
    HasSum (fun ij : I × J => ‖tensor (v ij.1) (w ij.2)‖^2) (a*b) := by
  simpa only [tensor_norm_sq] using hv.mul hw
    (hv.summable.mul_of_nonneg hw.summable (fun _ => sq_nonneg _) (fun _ => sq_nonneg _))

theorem tensor_entry [DecidableEq A] [DecidableEq B]
    {v : I → H A} {w : J → H B}
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    (a c : A) (b d : B) :
    inner ℂ (lp.single 2 (a,b) 1)
      (operator (fun ij : I × J => tensor (v ij.1) (w ij.2)) (lp.single 2 (c,d) 1)) =
      inner ℂ (lp.single 2 a 1) (operator v (lp.single 2 c 1)) *
      inner ℂ (lp.single 2 b 1) (operator w (lp.single 2 d 1)) := by
  apply (hasSum_entry (hasSum_tensor_norm hv.hasSum hw.hasSum).summable _ _).unique
  convert (hasSum_entry hv (lp.single 2 a 1) (lp.single 2 c 1)).mul
    (hasSum_entry hw (lp.single 2 b 1) (lp.single 2 d 1))
    (summable_mul_of_summable_norm
      (f := fun i => inner ℂ (lp.single 2 a 1) (v i)*inner ℂ (v i) (lp.single 2 c 1))
      (g := fun j => inner ℂ (lp.single 2 b 1) (w j)*inner ℂ (w j) (lp.single 2 d 1))
      (summable_entry_norm hv (lp.single 2 a 1) (lp.single 2 c 1))
      (summable_entry_norm hw (lp.single 2 b 1) (lp.single 2 d 1))) using 1
  ext ij
  simp only [lp.inner_single_left, lp.inner_single_right, tensor_apply, RCLike.inner_apply, map_mul, map_one]
  ring

theorem unitary_entry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {v : I → E} (hv : Summable (fun i => ‖v i‖^2))
    (U : E ≃ₗᵢ[ℂ] E) (x y : E) :
    inner ℂ x (operator (fun i => U (v i)) y) =
      inner ℂ (U.symm x) (operator v (U.symm y)) := by
  have hu : Summable (fun i => ‖U (v i)‖^2) := by simpa only [U.norm_map] using hv
  apply (hasSum_entry hu x y).unique
  convert hasSum_entry hv (U.symm x) (U.symm y) using 1
  ext i
  have h₁ : inner ℂ x (U (v i)) = inner ℂ (U.symm x) (v i) := by
    simpa only [U.apply_symm_apply] using U.inner_map_map (U.symm x) (v i)
  have h₂ : inner ℂ (U (v i)) y = inner ℂ (v i) (U.symm y) := by
    simpa only [U.apply_symm_apply] using U.inner_map_map (v i) (U.symm y)
  rw [h₁,h₂]

end TraceEnsemble

namespace EntropyPhotonNumber
open TensorLp
theorem beam_ensemble_entry {n : ℕ} {I J : Type*} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ : State n) (v : I → Fock n) (w : J → Fock n)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1)
    (hev : TraceEnsemble.operator v = ρ.op) (hew : TraceEnsemble.operator w = σ.op)
    (k l e : NumberIndex n) :
    inner ℂ (lp.single 2 (k,e) 1)
      (TraceEnsemble.operator (fun ij : I × J => beamUnitary η hη (tensor (v ij.1) (w ij.2)))
        (lp.single 2 (l,e) 1)) = outputBlock η ρ σ k l e := by
  rw [TraceEnsemble.unitary_entry (TraceEnsemble.hasSum_tensor_norm hv hw).summable]
  rw [beam_symm_number, beam_symm_number]
  simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold outputBlock
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [TraceEnsemble.tensor_entry hv.summable hw.summable, hev, hew]
  simp only [entry, numberKet]
  ring

end EntropyPhotonNumber

end

end OAI
