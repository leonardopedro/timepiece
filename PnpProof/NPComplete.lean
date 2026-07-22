import Mathlib

/-!
# K12.9 / NC: The NP-completeness closure theorem

This module formalizes the logical content the maintainer requested
(`PNP_IMPLEMENTATION_PLAN.md` K12.9, NC6/NC7): *"even a single problem in
`NP \ P` implies the NP-complete problem (e.g. SAT) is not in `P`."*

## Design — why the complexity model is left **abstract** (an honest deviation)

The plan (NC1–NC2) proposed a *concrete* polynomial-time predicate
`InP L := ∃ c k, ∀ x, Nat.Partrec.Code.evaln (Nat.size x ^ k + k) c x = some …`
using the fuel-indexed evaluator `evaln`. **This definition is not faithful**:
`Nat.Partrec.Code.evaln_bound` states that `x ∈ evaln K c n → n < K`, i.e. the
*fuel must strictly exceed the input value itself*, not merely the runtime. Since
`Nat.size x` grows like `log₂ x`, the fuel `Nat.size x ^ k + k` is eventually far
below `x`, so `evaln (Nat.size x ^ k + k) c x` is `none` for all large `x`.
Consequently the concrete `InP L` would be **vacuously false for every `L`**, and
every theorem about it (including `npc_not_inP`, and the claimed
`L_V_inP : InP L_V` of NC9) would be vacuously true / false — exactly the
"vacuous truth behind an unsatisfiable hypothesis" that soundness requires us to
avoid.

`evaln`'s fuel is a *value/recursion-depth* bound, not a step-count, and Mathlib
has no usable runtime-complexity API (`Turing.TM2ComputableInPolyTime` exists but
is essentially unpopulated — the plan itself records this in M5). A faithful
polynomial-time predicate is therefore a research-scale modelling project and is
**out of scope** (stop-and-report, per the plan's MODELLING/OPEN rules).

We therefore formalize the closure theorem **abstractly**, parameterized over a
`ComplexityModel` carrying `InP`, `InNP`, `ReducesP` together with the *one*
load-bearing property — **`P` is closed under polynomial-time reductions**
(NC4) — as a field. This is the genuine, non-vacuous logical content of NC6/NC7:
it holds for *any* faithful complexity model, and it isolates the closure
property NC4 as the hypothesis that a concrete (faithful) model would have to
discharge.

The honest mathematics underlying NC4 — that running a reduction and then a
decider composes into one machine — is recorded as the genuine, non-vacuous
`evaln` fact `evaln_comp_some`, and the polynomial-in-polynomial bookkeeping NC4
would need is recorded as `poly_comp`. Neither is vacuous; what is missing is
only the faithful *runtime* notion that would let them assemble into a concrete
`InP`.

## Fences (carried over)

* This is **not** the Clay statement and defines no Clay classes. Whether the
  `pnp.tex` model supplies a witness to the `∃ L, InNP L ∧ ¬ InP L` hypothesis is
  the OPEN crux (T5 / P5 / NC11), to be reported, never improvised.
* No axioms; no committed `sorry`.
-/

open Nat.Partrec

namespace PnpProof
namespace NPComplete

/-! ### NC1–NC2 basic data -/

/-- A language: a decision problem on (encoded) natural-number inputs. -/
abbrev Lang := ℕ → Bool

/-- The numeric encoding of a Boolean answer. -/
def toNat (b : Bool) : ℕ := bif b then 1 else 0

/-- Bit-length of an input (`Nat.size`). -/
def bitlen (x : ℕ) : ℕ := Nat.size x

/-! ### Genuine supporting mathematics (non-vacuous)

These are the real lemmas behind NC4's "composition of a reduction with a
decider". They hold unconditionally; only the faithful *runtime* wrapper that
would turn them into a concrete `InP` is missing (see the module docstring). -/

/-- **Polynomial-in-polynomial is polynomial** (the NC4 fuel arithmetic):
for any exponents `a, c` there is `d` with `(m^a + a)^c + c ≤ m^d + d` for every
`m`. (Used to bound a reduction's polynomial fuel substituted into a decider's
polynomial fuel.) -/
theorem poly_comp (a c : ℕ) :
    ∃ d, ∀ m : ℕ, (m ^ a + a) ^ c + c ≤ m ^ d + d := by
  refine ⟨(a + 1) * c + (1 + a) ^ c + c, fun m => ?_⟩
  set d := (a + 1) * c + (1 + a) ^ c + c with hd
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have hm1 : m ≤ 1 := by omega
    have h1 : m ^ a ≤ 1 := by
      calc m ^ a ≤ 1 ^ a := Nat.pow_le_pow_left hm1 a
        _ = 1 := one_pow a
    have h2 : (m ^ a + a) ^ c ≤ (1 + a) ^ c := Nat.pow_le_pow_left (by omega) c
    calc (m ^ a + a) ^ c + c ≤ (1 + a) ^ c + c := by omega
      _ ≤ d := by omega
      _ ≤ m ^ d + d := by omega
  · have ha : a ≤ m ^ a := by
      have h1 : a < 2 ^ a := Nat.lt_two_pow_self
      have h2 : 2 ^ a ≤ m ^ a := Nat.pow_le_pow_left hm a
      omega
    have hstep : m ^ a + a ≤ m ^ (a + 1) := by
      calc m ^ a + a ≤ m ^ a + m ^ a := by omega
        _ = 2 * m ^ a := by ring
        _ ≤ m * m ^ a := Nat.mul_le_mul_right _ hm
        _ = m ^ (a + 1) := by rw [pow_succ]; ring
    have hc : (m ^ a + a) ^ c ≤ (m ^ (a + 1)) ^ c := Nat.pow_le_pow_left hstep c
    have hpow : (m ^ (a + 1)) ^ c = m ^ ((a + 1) * c) := by rw [← pow_mul]
    have hmono : m ^ ((a + 1) * c) ≤ m ^ d := Nat.pow_le_pow_right (by omega) (by omega)
    calc (m ^ a + a) ^ c + c ≤ (m ^ (a + 1)) ^ c + c := by omega
      _ = m ^ ((a + 1) * c) + c := by rw [hpow]
      _ ≤ m ^ d + c := by omega
      _ ≤ m ^ d + d := by omega

/-
**Composition of codes via `evaln`** (the machine-level content of NC4):
if `cg` maps `x` to `y` and `cf` maps `y` to `z`, both within fuel `K+1`, then the
composite `comp cf cg` maps `x` to `z` within fuel `K+1`. (Both children run at
the same fuel — see `Nat.Partrec.Code.evaln`.)
-/
theorem evaln_comp_some (cf cg : Code) (K x y z : ℕ)
    (hg : y ∈ Code.evaln (K + 1) cg x) (hf : z ∈ Code.evaln (K + 1) cf y) :
    z ∈ Code.evaln (K + 1) (Code.comp cf cg) x := by
  simp_all +decide [ Nat.Partrec.Code.evaln ];
  have := Nat.Partrec.Code.evaln_bound hg; aesop;

/-! ### NC5–NC7 the abstract closure theorem -/

/-- An abstract complexity model: the predicates `InP`, `InNP`, the
polynomial-time many-one reduction `ReducesP`, and the load-bearing property
(NC4) that **`P` is closed under reductions**. A faithful Lean instantiation of
this structure is exactly what is missing (module docstring); the closure
theorem below holds for any instance. -/
structure ComplexityModel where
  /-- Languages decidable in polynomial time. -/
  InP : Lang → Prop
  /-- Languages verifiable in polynomial time (NP). -/
  InNP : Lang → Prop
  /-- Polynomial-time many-one reducibility. -/
  ReducesP : Lang → Lang → Prop
  /-- **NC4:** `P` is closed under polynomial-time reductions. -/
  P_closed : ∀ {L M : Lang}, ReducesP L M → InP M → InP L

set_option linter.dupNamespace false in
/-- **NC5:** `C` is NP-complete (in the model `Cx`): it is in NP and every NP
language reduces to it. -/
def NPComplete (Cx : ComplexityModel) (C : Lang) : Prop :=
  Cx.InNP C ∧ ∀ L, Cx.InNP L → Cx.ReducesP L C

/-- **NC6 — the closure theorem.** *A single language in `NP \ P` implies the
NP-complete problem is not in `P`.* -/
theorem npc_not_inP (Cx : ComplexityModel) {C : Lang} (hC : NPComplete Cx C)
    (h : ∃ L, Cx.InNP L ∧ ¬ Cx.InP L) : ¬ Cx.InP C := by
  obtain ⟨L, hLnp, hLnotP⟩ := h
  intro hCinP
  exact hLnotP (Cx.P_closed (hC.2 L hLnp) hCinP)

/-- **NC7 — specialisation to an NP-complete `SAT`.** If `SAT` is NP-complete and
*some* NP language is not in `P`, then `SAT ∉ P`. (`SAT`'s NP-completeness —
Cook–Levin, NC8 — is itself a major separate development; here it is the
hypothesis `hSAT`.) -/
theorem sat_not_inP (Cx : ComplexityModel) {SAT : Lang} (hSAT : NPComplete Cx SAT)
    (h : ∃ L, Cx.InNP L ∧ ¬ Cx.InP L) : ¬ Cx.InP SAT :=
  npc_not_inP Cx hSAT h

end NPComplete
end PnpProof
