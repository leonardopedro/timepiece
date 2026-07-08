Here is a rigorous, step-by-step formalization plan designed for a **Lean 4 / Mathlib** specialist. 

Since the full $L_{\omega_1, \omega_1}$ axioms used by Kopperman go too far (introducing unnecessary set-theoretic complexity and forcing deterministic PA), this plan is designed to be **constructive, modular, and logically weak** (aligning with the proof-theoretic strength of $\text{RCA}_0$ or $\text{ATR}_0$). 

The plan strictly separates the additive and multiplicative domains and defines the random map as a probability measure over a Polish space of configurations.

---

# Lean 4 Formalization Plan: The Decoupled Kopperman-Mehler Framework

## ★ IMPLEMENTATION STATE (2026-07-08) — read this first

The plan below is now largely ON DISK in `RiemannProof/RandomMap.lean` (1006 lines, registered
via `RiemannProof.lean:11`; compiles under `lake build RiemannProof` with warnings for exactly
one `sorry` — the named external citation of Step 7.2 — and the three `admit`s inside the
Phase 3 stub). Status per phase:

| Phase | Status |
|---|---|
| 1 (`NatAdd`, `NatMult`, `invIndex`, `summable_invIndex_sq`) | ✅ proved |
| 1.3 (`realize`, `realize_injective`) | ✅ proved (`RandomMap.lean:228`), exactly by the six-step recipe below |
| 1.3 Remark (`log_primes_linearIndependent`) | ✅ proved (`RandomMap.lean:745`, landed 2026-07-08) — `hp_indep` is discharged for the genuine primes, so `realize_injective` is unconditional there |
| 2 (`MapConfig` + topology) | `MapConfig` ✅ (`:331`); the topology instances are **discrete placeholders** (`⊥`, `:348–357`) — the pointwise-convergence Polish topology is open work |
| 3 (`mehlerPrior`) | **stub** (`:518–616`): a normalized Dirac-sum carrying the three `admit`s; the cylinder-set/projective-limit construction is open work |
| 4 (`HilbertSpaceConfig`, `basisVector_orthonormal`, `psiTrue`, `psiTruth`) | ✅ proved, domination/summability bounds included (`:400–474`) |
| 5–6 (`propHolds`, `measurable_set_propHolds`, `probabilityOfTruth`) | ✅ on disk (`:481`, `:504`, `:621`); `measurable_set_propHolds` currently proved *via the discrete placeholder* (trivially — every set is open) |
| 7.1 (`absolute_convergence_invariance`) | ✅ proved (`:661`) as recipe'd: `Equiv.summable_iff` + `Equiv.tsum_eq`, no order on the labels |
| 7.2 (`conditional_convergence_is_null`) | ✅ stated with the honest `hμ_exch` hypothesis and **closed by delegation** (`:727`) to the single named external input `random_rearrangement_divergence` (`:703`, sorry-bodied citation folding Hewitt–Savage + Kakutani per item 9's fallback); `measurable_set_ConvergentMaps` ✅ (`:673`, via the discrete placeholder); `NatAdd.ofNat`/`toNat_ofNat` ✅ (`:633`) |
| 8 (Strategy B — sampled scalars) | NEW spec (added 2026-07-08), nothing on disk yet |

The open work is organized as the numbered deliverable packages **RM1–RM14** in the
**★ WORK QUEUE** section immediately below; every implementation pass picks the lowest-numbered
package not yet ✅ (or any package the closing order marks as anytime-filler) and lands it.
Headline items: RM4 is a **design-critical no-go theorem** (fully exchangeable priors on
bijections cannot exist — it reshapes Phase 3 and Step 7.2 and is provable in a single pass);
RM9 builds the **block-shuffle prior**, a genuine diffuse probability measure that replaces the
Dirac-sum stub and yields a Kolmogorov zero–one dichotomy with **zero external input**; RM6
installs the Polish topology; RM10 is the Strategy-B almost-sure-independence theorem.

## ★ WORK QUEUE (2026-07-08) — deliverable packages RM1–RM14

Conventions, shared with `FORMALIZATION_ROADMAP.md`: every pass lands a numbered deliverable
from this queue and records it in the module docstring; external analytic inputs stay as
**named, docstring-cited `sorry`-bodied theorems** drawn from the explicit list in RM8/RM9
(the `bagchi_universality` practice) — formalize *around* them and shrink them only when a
numbered deliverable says so; computations end at small closed-form rationals (the roadmap's
STOP RULE #2 applies: no special-function or open-ended numerics). Sizes: S ≈ one short pass,
M ≈ one full pass, L ≈ several passes.

### RM1 (S) — Clock order API

Bundle the on-disk `toNat`/`ofNat` pair and give `NatAdd` its full Presburger interface
(order + addition — and nothing else; multiplication stays deliberately absent):

```lean
lemma NatAdd.ofNat_toNat (n : NatAdd) : NatAdd.ofNat n.toNat = n        -- induction on n
def NatAdd.equivNat : NatAdd ≃ ℕ := ⟨toNat, ofNat, ofNat_toNat, toNat_ofNat⟩
lemma NatAdd.toNat_add (a b : NatAdd) : (a + b).toNat = a.toNat + b.toNat
instance : AddCommMonoid NatAdd        -- from the add_comm/add_assoc/add_zero lemmas on disk
instance : LinearOrder NatAdd          -- transport along equivNat
lemma NatAdd.le_iff_toNat_le (a b : NatAdd) : a ≤ b ↔ a.toNat ≤ b.toNat
  -- and: the transported order agrees with the on-disk inductive `le`
instance : Denumerable NatAdd          -- Denumerable.ofEquiv via equivNat
```

Payoff: every later package indexes the clock through `equivNat` instead of ad-hoc `toNat`
plumbing; `Denumerable NatAdd` feeds RM3.

### RM2 (S–M) — Labels API

```lean
instance {P} [Countable P] : Countable (NatMult P)      -- Multiset = quotient of List
instance {P} [Nonempty P] : Infinite (NatMult P)        -- n ↦ replicate n witness, injective
instance {P} [Encodable P] : Denumerable (NatMult P)    -- via Mathlib's List/Multiset encodings
lemma NatMult.omega_mul (x y : NatMult P) : (x * y).omega = x.omega + y.omega
lemma NatMult.omega_one : (1 : NatMult P).omega = 0
def realizeHom (hp : ∀ i, 0 < p i) : NatMult P →* ℝ     -- realize_one, realize_mul
lemma one_le_realize (hp : ∀ i, 1 ≤ p i) (n : NatMult P) : 1 ≤ realize p n
lemma realize_pos (hp : ∀ i, 0 < p i) (n : NatMult P) : 0 < realize p n
```

`realize_mul` is `Multiset.map_add` + `Multiset.prod_add` (the label product is multiset
union). Keep the labels order-free throughout: no `LE (NatMult P)` instance, ever — that
absence is Phase 1's whole point.

### RM3 (S) — Nonemptiness of `MapConfig` and the canonical dictionary

```lean
noncomputable def canonicalConfig (P) [Denumerable P] : MapConfig P :=
  NatAdd.equivNat.trans (Denumerable.eqv (NatMult P)).symm
instance {P} [Denumerable P] : Nonempty (MapConfig P) := ⟨canonicalConfig P⟩
```

(For the `[Countable P] [Nonempty P]` generality, route through
`Denumerable.mk'`/`Encodable.ofCountable`.) This **removes the third `admit`** in the Phase 3
stub and provides the base point that RM9 shuffles.

### RM4 (M) — ★ DESIGN-CRITICAL: the exchangeability no-go theorem

Full exchangeability is *impossible* for a countably-additive probability measure on
bijections into a countable label set — the hypothesis `hμ_exch` of the on-disk Step 7.2 can
never be discharged. Formalize this; the proof is elementary and needs no de Finetti:

```lean
theorem no_exchangeable_bijection_prior {P} [Countable P] [Nonempty P]
    (μ : Measure (MapConfig P)) [IsProbabilityMeasure μ]
    (hμ_exch : ∀ σ : Equiv.Perm NatAdd, (∃ s : Finset NatAdd, ∀ x ∉ s, σ x = x) →
      MeasurePreserving (fun ω : MapConfig P => (σ : NatAdd ≃ NatAdd).trans ω) μ μ) :
    False
```

Proof sketch: let `a m := μ {ω | ω 0 = m}`. (1) For each clock tick `i`, the swap
`Equiv.swap 0 i` is finitely supported, and `hμ_exch` applied to it gives
`μ {ω | ω i = m} = a m`. (2) For fixed `m`, the events `{ω | ω i = m}` (over `i`) are pairwise
disjoint because each `ω` is injective; countable additivity gives `∑ᵢ a m ≤ 1`, forcing
`a m = 0` for every `m`. (3) `Set.univ = ⋃ m, {ω | ω 0 = m}` is a countable union
(`Countable (NatMult P)`, RM2), so `1 = μ Set.univ = ∑' m, a m = 0` — contradiction.
Measurability of the coordinate events is free under the current `borel`-of-discrete instance
and stays free after RM6 (they are cylinder sets). Follow-ups inside the same package:

* re-docstring the on-disk `conditional_convergence_is_null` and
  `random_rearrangement_divergence` to record that their hypothesis is vacuous for genuine
  probability measures (the theorems stay — they are true — but RM9 supplies the non-vacuous
  replacement);
* add the same note to the Phase 3/Step 7.2 prose of this plan (a one-line pointer to RM4 at
  each site suffices).

### RM5 (M) — Toy model with a rational answer

The honest finite toy truncates *both* sorts: a finite clock `Fin k` against `k` chosen labels.

```lean
def ToyConfig (k : ℕ) := Fin k ≃ Fin k                    -- dictionaries of the truncated world
noncomputable def toyPrior (k : ℕ) : Measure (ToyConfig k) -- uniform: PMF.uniformOfFintype .toMeasure
noncomputable def toyProbabilityOfTruth (k) (P_test : Fin k → Bool) : ℝ
example : toyProbabilityOfTruth 2 (fun i => i = 0) = 1/2 := by decide/norm_num-style proof
```

Also prove the sanity endpoints `P_test ≡ true ⇒ 1` and `P_test ≡ false ⇒ 0` at the toy level.
Stop at small rationals; the toy exists to check that measure and geometry compose, not to
compute anything.

### RM6 (L) — The Polish topology package (replaces the discrete placeholders)

Install the genuine topology of pointwise convergence *in both directions* (the standard
`S_∞` presentation — one-sided pointwise convergence does not make the bijections a closed
subspace, the two-sided embedding does):

```lean
def MapConfig.embed (ω : MapConfig P) : (NatAdd → NatMult P) × (NatMult P → NatAdd) :=
  (ω, ω.symm)
instance : TopologicalSpace (MapConfig P) := .induced MapConfig.embed inferInstance
theorem MapConfig.isClosedEmbedding : IsClosedEmbedding (MapConfig.embed (P := P))
instance : PolishSpace (MapConfig P)       -- closed subspace of a Polish product of discretes
theorem continuous_eval (n : NatAdd) : Continuous fun ω : MapConfig P => ω n
theorem isClopen_cylinder (n m) : IsClopen {ω : MapConfig P | ω n = m}
theorem borel_eq_generateFrom_cylinders : ‹the Borel σ-algebra is generated by the cylinders›
```

Then re-prove, against the real topology, the two theorems that currently ride the placeholder:
`measurable_set_propHolds` (via RM7's coordinate lemma: a countable intersection of clopen
cylinders, hence closed and measurable) and `measurable_set_ConvergentMaps` (the sorted Cauchy
criterion: `⋂_{ε ∈ ℚ⁺} ⋃_N ⋂_{M,M'>N}` of events depending on finitely many coordinates).
Sub-deliverable freebies worth registering: `T2Space`, `TotallyDisconnectedSpace`, and
continuity of composition and inversion (`MapConfig` as a topological group under `.trans`).

### RM7 (M) — The geometry–logic bridge lemmas

The file defines `propHolds` but never yet proves it *means* "true at every tick" — the
Kopperman translation deserves its theorem:

```lean
theorem propHolds_iff (ω : MapConfig P) (P_test) :
    propHolds ω P_test ↔ ∀ n, P_test (ω n) = true
  -- lp coefficient extensionality + invIndex n ≠ 0
theorem dist_sq_eq_tsum_missed (ω) (P_test) :
    ‖psiTrue ω - psiTruth ω P_test‖ ^ 2
      = ∑' n : {n : NatAdd // P_test (ω n) = false}, (NatAdd.invIndex n) ^ 2
theorem propHolds_monotone : (∀ x, P_test x = true → Q_test x = true) →
    propHolds ω P_test → propHolds ω Q_test
```

`dist_sq_eq_tsum_missed` is the quantitative Kopperman statement — distance measures exactly
the weighted mass of counterexample ticks. Uses `lp.norm_rpow_eq_tsum` (p = 2) and the
domination bound already on disk.

### RM8 (L) — The global prior: Fisher–Yates on the clock (Kakutani strength)

The full "non-summable ⇒ null event" conclusion needs *global* randomization (RM9 proves local
shuffles genuinely fail it). Construct the geometric Fisher–Yates dictionary: fix
`canonicalConfig` (RM3) as the label enumeration; sample `G₀, G₁, …` i.i.d. geometric(1/2) on
ℕ; tick `n` receives the `Gₙ`-th *not-yet-used* label.

* **RM8a**: the kernel chain and its infinite product — via Mathlib's Ionescu–Tulcea
  (`Mathlib/Probability/Kernel/IonescuTulcea/`, in the vendored checkout; if the API resists,
  build the joint law on `ℕ → ℕ` with `Measure.infinitePi` and define the assembly map from
  rank sequences to injections).
* **RM8b**: a.s. totality/surjectivity — every label is eventually consumed; second
  Borel–Cantelli (independent events with divergent probability sum;
  `ProbabilityTheory.measure_limsup_eq_one`) — yielding `fisherYatesPrior : Measure (MapConfig P)`,
  `IsProbabilityMeasure`, and `NoAtoms`-style diffuseness.
* **RM8c**: quasi-invariance under finitely-supported clock permutations (law of `ω ∘ σ` is
  absolutely continuous w.r.t. the law of `ω`, with an explicit finite-product density) — the
  honest surrogate for the exchangeability RM4 forbids; null events are permutation-stable.
* **RM8d**: the narrowed external input. Retire the current wide citation in favor of the
  named, docstring-cited `sorry` `fisher_yates_divergence : ¬ Summable c →
  fisherYatesPrior (ConvergentMaps c) = 0` (Kakutani-problem strength, global rearrangement),
  and re-derive `conditional_convergence_is_null`-for-`fisherYatesPrior` from it plus RM8c.
  The external-input list for this file is exactly: {Hewitt–Savage (until Mathlib grows it),
  Kakutani-type global divergence}. Everything else is proved.

### RM9 (L) — The block-shuffle prior: a real diffuse prior with a PROVABLE zero–one law

Adopt as the interim `mehlerPrior` (replacing the Dirac-sum stub, which retires the remaining
two `admit`s): partition the clock into consecutive blocks `B_k` with `|B_k| = k + 1`, put the
uniform law on each finite symmetric group `Equiv.Perm (Fin (k+1))`, take the countable product
(`Measure.infinitePi` of finite uniforms — no projective-limit subtleties, every factor is a
`Fintype`), and push forward along the assembly map `(π_k)_k ↦ canonicalConfig ∘ (blockwise π)`.
Every sample is a genuine bijection *deterministically* — no a.s.-surjectivity work at all.

* **RM9a**: `blockShufflePrior : Measure (MapConfig P)`, `IsProbabilityMeasure`, measurability
  of the assembly map (coordinates of the image depend on one factor each).
* **RM9b**: diffuseness — each singleton has measure `≤ ∏_{k ≤ K} 1/(k+1)! → 0`.
* **RM9c**: invariance under block-preserving finite permutations (the subgroup replacing RM4's
  impossible full exchangeability).
* **RM9d — the headline, zero external input**: `ConvergentMaps c` ignores any finite set of
  block factors (changing finitely many blocks changes finitely many partial sums), so it is a
  tail event of an independent family; Mathlib's **Kolmogorov zero–one law**
  (`Mathlib/Probability/Independence/ZeroOne.lean`) gives
  `blockShufflePrior (ConvergentMaps c) = 0 ∨ blockShufflePrior (ConvergentMaps c) = 1` —
  the first dichotomy theorem of the development proved entirely inside Mathlib.
* **RM9e — the honest boundary**: prove the *counterexample* showing local shuffles cannot
  reach Kakutani strength: for the alternating-harmonic family pulled back along
  `canonicalConfig`, **every** block-preserving rearrangement converges (within a block the
  total variation is `≤ ∑_{n ∈ B_k} |c n| ≈ 1/k → 0`, and block-boundary partial sums are
  rearrangement-invariant), so `¬ Summable c` with `blockShufflePrior (ConvergentMaps c) = 1`.
  This theorem is why RM8 exists, and it is fully provable — a deterministic statement about
  finite rearrangements plus a series estimate.

### RM10 (L) — Strategy B: almost-sure multiplicative independence

On the product space `ℕ → ℝ` with `μ = Measure.infinitePi (fun _ => ν)` for an atomless
probability measure `ν` supported in `(1, ∞)`:

* **RM10a**: single-relation nullity — for each nonzero `q : ℕ →₀ ℚ`,
  `μ {x | ∑ i ∈ q.support, (q i : ℝ) * Real.log (x i) = 0} = 0`: pick `j` with `q j ≠ 0`,
  factor `μ` through the `j`-th coordinate (Fubini for `infinitePi`), and for a.e. fixing of
  the other coordinates the relation pins `x j` to one point — an atomless-null event
  (`Real.log` injective on `(0,∞)`).
* **RM10b**: countability of `{q : ℕ →₀ ℚ | q ≠ 0}` (`Finsupp` over countable types is
  countable) and the union bound (`measure_iUnion_null_iff`).
* **RM10c**: the headline
  `ae_log_linearIndependent : ∀ᵐ x ∂μ, LinearIndependent ℚ (fun i => Real.log (x i))`
  (bridge via `linearIndependent_iff'` — a violation IS a nonzero finitely-supported relation),
  plus the corollary `∀ᵐ x ∂μ, Function.Injective (realize (x ∘ decode))` through
  `realize_injective`: **unique factorization almost surely**, the sampled twin of
  `log_primes_linearIndependent`.
* **RM10d**: one concrete instantiation, `ν = (volume.restrict (Set.Ioo 1 2)).toProbability`-style
  uniform law, with its atomlessness instance.

### RM11 (S, recurring) — Docstring discipline sweeps

Keep Action Plan items 7 and 11 current as packages land: every new convergence or
completeness lemma carries the sorted-quantifier paragraph (bounded vector indices, unbounded
quantifier on the clock) and, where a measure is involved, the Strategy-B M-samples reading.
One sweep after each L-package counts as a deliverable.

### RM12 (M) — Probability endpoints and monotonicity

Once RM9a lands (any genuine probability prior), tie the knot Phase 6 promises:

```lean
theorem probabilityOfTruth_of_true : probabilityOfTruth (fun _ => true) = 1
  -- propHolds holds for every ω (RM7), truth set = univ
theorem probabilityOfTruth_of_false : probabilityOfTruth (fun _ => false) = 0
  -- coefficients differ at tick 0 (invIndex ≠ 0), truth set = ∅
theorem probabilityOfTruth_mono :
    (∀ x, P_test x = true → Q_test x = true) →
    probabilityOfTruth P_test ≤ probabilityOfTruth Q_test   -- RM7 monotone + measure_mono
```

These three lines are the page's "probability of a proposition" story made checkable
end-to-end: 1 for tautologies, 0 for antilogies, monotone in logical strength.

### RM13 (M–L, stretch) — Beurling counting finiteness

With escape-to-infinity primes (`hp₂ : Filter.Tendsto p Filter.cofinite Filter.atTop`,
`hp₁ : ∀ i, 1 < p i` — satisfied by the genuine primes), the Beurling integers are locally
finite: `theorem finite_realize_le (x : ℝ) : {n : NatMult P | realize p n ≤ x}.Finite`
(only finitely many primes fit under `x`; multiset exponents are bounded by `log x / log`
of the smallest prime; inject into a finite product of ranges). This is the first brick of any
future Beurling-zeta work and a self-contained combinatorial exercise until then.

### RM14 (S–M) — Import hygiene and the axiom audit

Replace the blanket `import Mathlib` with the per-phase module imports this plan already lists;
run `#print axioms` on the headline theorems (`realize_injective`,
`log_primes_linearIndependent`, `absolute_convergence_invariance`, and each new RM headline as
it lands) and record the outcome (the standard trio, plus `sorryAx` exactly on the named
external inputs) in the module docstring — the checkable form of Action Plan item 1.

### Closing order

A pass that starts NOW does, in order: **RM1 → RM2 → RM3 → RM4** (each unblocked, RM4 is the
design-critical one), then **RM7 → RM6 → RM9 → RM5 → RM12**, then **RM10**, then **RM8**, with
**RM11/RM13/RM14** as anytime fillers. Every package is written to be landable without waiting
on the author; when the author promotes new work for this file, its entry supersedes this
paragraph.

## Phase 1: Separating the Additive and Multiplicative Naturals
We must enforce the logical separation of the "clock" (addition only) and the "data" (multiplication only) at the type level.

### Step 1.1: The Additive-Only Naturals ($\mathbb{N}_+$)
We define the sequential indexing structure. This is isomorphic to the standard natural numbers but strictly exposes only the additive/order structure (Presburger Arithmetic).
```lean
import Mathlib.Algebra.Order.Monoid.Defs

/-- The additive-only natural numbers (Presburger clock) -/
inductive NatAdd where
  | zero : NatAdd
  | succ : NatAdd → NatAdd
  deriving DecidableEq, Repr

namespace NatAdd

def add : NatAdd → NatAdd → NatAdd
  | zero, y => y
  | succ x, y => succ (add x y)

instance : Add NatAdd := ⟨add⟩

def le : NatAdd → NatAdd → Prop
  | zero, _ => True
  | succ _, zero => False
  | succ x, succ y => le x y

instance : LE NatAdd := ⟨le⟩
-- Note: Do NOT define multiplication (*) on NatAdd.
end NatAdd
```

### Step 1.2: The Multiplicative-Only Naturals ($\mathbb{N}_\times$)
We define the basis labels. This is a free commutative monoid generated by a countable set representing Beurling primes. It has no addition operator.
```lean
import Mathlib.Algebra.FreeMonoid.Basic

/-- Representing the count of Beurling primes as a countable type -/
variable (BeurlingPrimes : Type) [Countable BeurlingPrimes]

/-- The multiplicative-only naturals (Skolem basis) -/
def NatMult := FreeCommMonoid BeurlingPrimes
-- Note: This type naturally has a multiplication operator `*` and unit `1`, 
-- but no addition operator `+`.
```

---

### Step 1.3: Realizing the Beurling Primes as Reals (the Gödelian Safety Shield)

The abstract type `BeurlingPrimes` above is deliberately uncommitted as to *what* the primes
are. Realize them concretely as a countable family of multiplicatively independent real numbers
greater than 1 — e.g. $p_0=\sqrt2,\ p_1=e,\ p_2=\pi,\dots$ — rather than as formal atoms, and let
a label evaluate to an honest real number by taking the product over its prime factorization:

```lean
import Mathlib.Analysis.SpecialFunctions.Log.Basic

variable (p : BeurlingPrimes → ℝ) (hp_one_lt : ∀ i, 1 < p i)
  (hp_indep : LinearIndependent ℚ (fun i => Real.log (p i)))

/-- A Beurling integer (an element of `NatMult`) evaluates to a real number by taking
    the product over its multiset of prime factors. Log-independence of the `p i`
    (multiplicative independence) makes this map injective — unique factorization. -/
noncomputable def realize (n : NatMult BeurlingPrimes) : ℝ := (n.map p).prod
```

This one design choice closes the last possible gap back to Peano arithmetic, for two
independent reasons:

1.  **Julia Robinson's theorem does not fire.** Her 1949 result that $\langle\mathbb N,\times,<\rangle$
    alone defines $+$ relies on the rigid, uniform $+1$ gap of the standard integers — that $n$
    and $n+1$ are always coprime and nothing lies between them. Because the `p i` are chosen as
    multiplicatively independent reals rather than the standard primes marching over a fixed
    lattice, the image of `realize` is an irregularly spaced set of reals with no uniform gap at
    all. Robinson's construction of $+$ from $\times$ and $<$ has nothing rigid to grab onto, so
    `NatMult`'s order and product cannot reconstruct `NatAdd`'s successor structure.
2.  **Tarski's real closed field absorbs the operations, and its quantifier-elimination theorem
    forbids ever isolating the image.** Since `realize` lands in $\mathbb R$, the $\times$ and $<$
    used on labels are literally Tarski's RCF operations, whose complete first-order theory is
    decidable. Tarski's quantifier elimination further shows that no first-order formula over
    $\mathbb R$ can define an infinite discrete subset such as the image of `realize`. Without a
    definable set to induct over, no first-order induction schema over the Beurling integers can
    even be *stated*, let alone used to reconstruct Gödel's diagonal argument.

Net effect: the type-level split of Phase 1 (`NatAdd` vs. `NatMult`) is not merely a typing
discipline we promise to maintain — it is backed by an external, non-formalized theorem pair
(Robinson 1949; Tarski 1951) guaranteeing that no bridge we could build back from labels to
clock, however clever, can smuggle Peano's undecidability in from the multiplicative side alone.
The only place undecidability could possibly re-enter is the identification map itself — which
is exactly the object Phase 2 onward puts a probability measure over, instead of asserting.

#### Recipe for the Lean specialist: `realize_injective`

**Status: ✅ landed** — `realize_injective` is proved on disk (`RandomMap.lean:228`) exactly by
steps 1–6 below; the recipe is retained as documentation of the proof.

Action Plan item 6 asks for `Function.Injective (realize p)` given `hp_indep`. This has been
worked out end-to-end against the project's vendored Mathlib checkout
(`.lake/packages/mathlib`, pinned v4.28.0) so the specialist has a checked recipe rather than a
blank page. State it (inside `namespace NatMult`, so `[DecidableEq P]` is already in scope) as:

```lean
theorem realize_injective (hp_pos : ∀ i, 0 < p i)
    (hp_indep : LinearIndependent ℚ (fun i : P => Real.log (p i))) :
    Function.Injective (realize p) := by
  ...
```

and prove it in six steps, each keyed to a specific Mathlib lemma:

1.  **Logs turn the product equality into a sum equality.** For `hp_ne : ∀ i, p i ≠ 0` (from
    `hp_pos`), use `Real.log_multiset_prod {s : Multiset ℝ} (h : ∀ x ∈ s, x ≠ 0) : Real.log
    s.prod = (s.map Real.log).sum` on `s := n.map p`, then `Multiset.map_map` to fold
    `(n.map p).map Real.log` into `n.map (Real.log ∘ p)`. Applied to both `n₁` and `n₂` and
    chained through `congrArg Real.log h`, this gives
    `(n₁.map (Real.log ∘ p)).sum = (n₂.map (Real.log ∘ p)).sum`.
2.  **Multiset sums become count-weighted `Finset` sums.** Use
    `Finset.sum_multiset_map_count (s : Multiset ι) (f : ι → M) [DecidableEq ι] [AddCommMonoid M]
    : (s.map f).sum = ∑ m ∈ s.toFinset, s.count m • f m` (the `to_additive` sibling of
    `Finset.prod_multiset_map_count`) on both sides.
3.  **Extend both sums to the common support** `s := n₁.toFinset ∪ n₂.toFinset` via
    `Finset.sum_subset (h : s₁ ⊆ s₂) (hf : ∀ x ∈ s₂, x ∉ s₁ → f x = 0) : ∑ i ∈ s₁, f i = ∑ i ∈
    s₂, f i`, using `Finset.subset_union_left` / `Finset.subset_union_right` and
    `Multiset.count_eq_zero_of_not_mem` to discharge `hf`.
4.  **Convert `ℕ`-`nsmul` to real multiplication** (`nsmul_eq_mul`) and split the resulting
    difference with `Finset.sum_sub_distrib`, `sub_eq_zero`, to land on
    `∑ m ∈ s, ((n₁.count m : ℝ) − (n₂.count m : ℝ)) * Real.log (p m) = 0`.
5.  **Feed this into log-independence.** Set `g : P → ℚ := fun m => (n₁.count m : ℚ) −
    (n₂.count m : ℚ)`; note `g m • Real.log (p m) = (↑(g m) : ℝ) * Real.log (p m)` by
    `Rat.smul_def (a : ℚ) (x : K) [DivisionRing K] : a • x = ↑a * x`, so step 4's equation is
    exactly `∑ m ∈ s, g m • (fun i => Real.log (p i)) m = 0`. Apply
    `linearIndependent_iff' : LinearIndependent R v ↔ ∀ s, ∀ g, (∑ i ∈ s, g i • v i = 0) → ∀ i ∈
    s, g i = 0` (with `R := ℚ`, `v := fun i => Real.log (p i)`) to get `∀ m ∈ s, g m = 0`, i.e.
    `n₁.count m = n₂.count m` (cast back from `ℚ` to `ℕ`) for every `m` in the common support.
6.  **Close with `Multiset.ext`.** `Multiset.ext {s t : Multiset α} [DecidableEq α] : s = t ↔ ∀
    a, s.count a = t.count a`. For `a ∈ s` use step 5; for `a ∉ s`, `a` is in neither `n₁.toFinset`
    nor `n₂.toFinset`, so both counts are `0` by `Multiset.count_eq_zero_of_not_mem` directly.

None of steps 1–6 needs Robinson's or Tarski's theorems themselves (per Action Plan item 6) —
`hp_indep` is taken as the one external hypothesis, exactly the log-independence fact those
theorems justify choosing `p` to satisfy.

#### Remark: the genuine primes suffice — Beurling generality is optional

Nothing in the framework requires the primes to be exotic. `P` may be instantiated with the
ordinary rational primes, `P := {q : ℕ // q.Prime}` with `p := fun q => (q : ℝ)`, *taken as a
bare unordered countable type*: the load-bearing safety requirement was never irregular spacing
per se, but the refusal to install an order on the labels or identify them with the additive
clock — the identification is exactly what Phase 2 randomizes. Under this instantiation the
shield's division of labor shifts but both halves stand: Robinson's construction is defeated by
pure type discipline (the ordered structure $\langle \mathbb N, \times, < \rangle$ her theorem
needs is simply never assembled, because no order is installed on `P`), and Tarski's half is
unchanged — $\mathbb N \subset \mathbb R$ is the *canonical* example of a set undefinable in
RCF. What the Beurling generalization buys is insurance, not necessity: irregularly spaced
primes would defeat Robinson even if the ambient real order leaked onto the labels.

The instantiation also *upgrades* Step 1.3: `hp_indep` stops being a hypothesis and becomes a
provable lemma, because ℚ-linear independence of `fun q : P => Real.log (q : ℝ)` *is* the
fundamental theorem of arithmetic in logarithmic dress. The vendored Mathlib has no ready-made
`linearIndependent` statement for logs of primes (checked), but the proof is elementary and the
pins exist: from a vanishing rational combination, clear denominators and exponentiate to get an
equality of two natural-number products of prime powers, then compare exponents via unique
factorization — `Nat.factorizationEquiv` (unique factorization as an `Equiv` between `ℕ+` and
prime-supported finsupps), `Nat.factorization_prod_pow_eq_self`, and `Nat.eq_factorization_iff`
(`Mathlib/Data/Nat/Factorization/Basic.lean:86` and nearby). Call the new lemma
`log_primes_linearIndependent`; feeding it to `realize_injective` makes injectivity
*unconditional* for the genuine primes.

**Status: ✅ landed (2026-07-08)** — `log_primes_linearIndependent` is proved on disk
(`RandomMap.lean:745`). The executed proof follows the FTA route sketched above but directly
rather than through `Nat.factorizationEquiv`: clear denominators to integer coefficients, split
the support into positive- and negative-exponent halves, exponentiate the vanishing log-sum
(`Real.exp_sum`, `Real.log_zpow`, `Real.exp_log`) into an equality of two natural-number
products of prime powers, and close with a prime-divisibility comparison forcing every exponent
to zero.

---

## Phase 2: Defining the Configuration Space (The Mappings)
We define the space of all possible ways to map our additive clock to our multiplicative basis. This space represents the "configurations of the universe."

```lean
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Category.TopCat.Basic

/-- An equivalence (bijection) between the additive and multiplicative naturals -/
def MapConfig (P : Type) [Countable P] := NatAdd ≃ NatMult P

-- Mathlib Task: 
-- 1. Equip `NatAdd` with the discrete topology.
-- 2. Equip `NatMult` with the discrete topology.
-- 3. Equip `MapConfig` with the topology of pointwise convergence (inducing a Polish space).
```

*Status:* `MapConfig` ✅ on disk (`RandomMap.lean:331`); tasks 1–2 ✅; task 3 is on disk only as
a **discrete placeholder** (`⊥` on `MapConfig` itself, `RandomMap.lean:356`) — installing the
genuine pointwise-convergence topology is ★ work-queue package RM6, and doing so also upgrades the two
measurability theorems (Phases 6 and 7.2) from placeholder proofs (every set open) to real ones.

---

## Phase 3: Setting Up the Probability Measure (Mehler Prior)
We construct the probability space over the configurations. Since `MapConfig` is a Polish space, we can rigorously define Borel measures on it without needing ZFC.

```lean
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.MeasurableSpace.Basic

open MeasureTheory

variable {P : Type} [Countable P]

/-- The Borel sigma-algebra on the configuration space -/
instance : MeasurableSpace (MapConfig P) := BorelSpace.toMeasurableSpace

/-- The Mehler prior probability measure on the space of all mappings -/
noncomputable def mehlerPrior : Measure (MapConfig P) :=
  sorry -- To be defined as a probability measure (total mass 1)
```

*Status:* on disk (`RandomMap.lean:518`) as a normalized Dirac-sum **stub** carrying three
`admit`s (an injective encoding it does not have, the mass bound, and nonemptiness of
`MapConfig P`); it type-checks the downstream API but is neither diffuse nor exchangeable. The
construction deliverable is now **RM9** (the block-shuffle prior — a genuine diffuse
probability measure whose product-of-finite-uniforms form sidesteps the projective-limit
subtleties; RM3 retires the nonemptiness `admit` first), with **RM8** (Fisher–Yates) as the
stronger global prior behind it. One warning has been discovered since this phase was written:
by **RM4**, *no* countably-additive probability measure on `MapConfig P` is exchangeable under
all finitely-supported clock permutations, so full exchangeability is not a property any
construction can deliver — RM9c's block-preserving invariance and RM8c's quasi-invariance are
the correct surrogates.

---

## Phase 4: Constructing the Hilbert Space over the Random Map
Instead of a single, deterministic Hilbert space, we define a Hilbert space parameterized by the mapping $\omega \in \text{MapConfig}$.

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.NormedSpace.lpSpace

open Hilbert

/-- For a given mapping ω, the Hilbert space is represented by l^2(NatAdd) -/
def HilbertSpaceConfig (ω : MapConfig P) := lp (fun (_ : NatAdd) => Real) 2

-- Mathlib Task:
-- Define the standard orthonormal basis vectors `e_n` in this space.
```

*Status:* ✅ — `HilbertSpaceConfig`, `basisVector` (`lp.single`), and `basisVector_orthonormal`
(⟨e_n, e_m⟩ = δ_{n,m}) are proved on disk (`RandomMap.lean:400–431`).

### Step 4.1: Completeness Without Infinite Objects (the Sorted Cauchy Condition)

Step 1.3 closed the definability loophole on the *labels*; there is one more place a Gödelian
ghost could hide, and it is in the *analysis*. In a first-order real closed field one cannot
define or quantify over an arbitrary completed infinite sequence of reals as a single object —
if one could, the field could carve out the integers inside itself, and Tarski's quantifier
elimination (and with it decidability) would instantly collapse. A naive statement of Hilbert
space completeness quantifies over exactly such infinite sequences. So completeness must be
stated in a form where the scalar sort never sees an infinite object. The Cauchy condition
admits precisely such a sorted formulation, with every vector index bounded:

$$ \forall \epsilon > 0 \quad \exists N \quad \forall M > N \quad \forall n, m \;\; (N < n, m < M \implies \| x_n - x_m \| < \epsilon) $$

Three observations make this work:

1.  **Bounded indices keep the scalars finite-dimensional.** For each fixed $M$, the segment
    $(x_1, \dots, x_M)$ is not an infinite object — it is a single point of $\mathbb R^M$, and
    finite tuples of reals, their norms, and their comparisons are exactly what Tarski's RCF
    defines and decides, no matter how large $M$ grows. The scalar sort only ever evaluates the
    metric on finite-dimensional spaces.
2.  **The one unbounded quantifier lives in the Presburger sort.** The $\forall M > N$ ranges
    over the additive clock (`NatAdd`), a separate sort where unbounded quantification is safe:
    Presburger arithmetic is complete and decidable. The clock ticks out ever-larger finite
    bounds; for each bound, the reals check a finite tuple. Infinity is handed entirely to the
    sort that can carry it.
3.  **Completeness becomes constructive metric completion.** The Hilbert space is not asserted
    into existence as a set of infinite sequences; it is the limit of the finite-dimensional
    spaces $\mathbb R^M$ as $M$ grows under the clock. This is the ultimate form of the
    "decidable dense subset": Tarski reals for finite-dimensional geometry, Presburger
    arithmetic as the finite-approximation clock, Beurling semigroups as the multiplicative
    basis — every axiomatic step decidable.

A precision worth recording: **the sorted condition is not first-order — and that is the
mechanism, not a defect.** Because the quantifiers $\exists N$ and $\forall M$ range over the
clock sort, the displayed condition is a *multi-sorted* (second-order-like relative to the
field) statement, not a formula of RCF. This is exactly why the shield of Step 1.3 survives the
analysis: the completeness statement never enters the scalar sort's own first-order language, so
Tarski's quantifier elimination and decidability are never confronted with it.

The multi-sorted reading also buys a **constructive-emergence upgrade**. The scalar sort need
not start as the full continuum: any model of RCF will do — in particular the countable, fully
computable field of real algebraic numbers $\mathbb R_{\text{alg}}$ (RCF is complete, so
$\mathbb R_{\text{alg}}$ is elementarily equivalent to $\mathbb R$). $\mathbb R_{\text{alg}}$ is
an Archimedean ordered field, and an Archimedean ordered field has a *unique* metric completion
— so the multi-sorted Cauchy completion of $\mathbb R_{\text{alg}}$ is uniquely isomorphic to
the standard, uncountable $\mathbb R$, transcendentals ($\pi$, $e$, Euler's $\gamma$) included.
Where classical foundations postulate the uncountable continuum as a static, pre-existing black
box, this framework postulates only a decidable first-order field and the additive clock, and
the continuum *emerges* as the completed geometric workspace.

For the Lean specialist this costs nothing new: Mathlib's `lp … 2` *is* the constructive metric
completion of the finitely supported sequences, and its `CauchySeq`/`Summable` infrastructure
already factors every convergence statement through `Finset`-indexed partial sums — i.e. through
finite tuples with the unbounded quantifier on the index sort. The deliverables of Action Plan
item 4 automatically have the sorted shape; the item below just asks that this be recorded.
The emergence point is likewise already how the library works, not a new obligation: Mathlib's
`Real` is *defined* as equivalence classes of Cauchy sequences of $\mathbb Q$
(`Mathlib/Data/Real/Basic.lean`, `structure Real where ofCauchy :: cauchy :
CauSeq.Completion.Cauchy (abs : ℚ → ℚ)`) — a constructed completion of a countable decidable
field, not a postulated continuum — and uniqueness of Archimedean completions means completing
$\mathbb Q$ or $\mathbb R_{\text{alg}}$ lands in the same $\mathbb R$. Record this in the
docstrings per Action Plan item 7; do not build a separate $\mathbb R_{\text{alg}}$ in Lean.

---

## Phase 5: Formulating the Metric Proposition
We define the truth-vector of an arithmetic proposition (like the Riemann Hypothesis via its Diophantine equivalent) as a function of the configuration $\omega$.

```lean
variable (DecidableTest : NatMult P → Bool)

/-- The "All-True" target vector: ∑ (1/n) |e_n⟩ -/
noncomputable def psiTrue (ω : MapConfig P) : HilbertSpaceConfig ω :=
  sorry -- Defined as the convergent sum of (1/n) * e_n

/-- The "Truth-Vector" for a given configuration ω -/
noncomputable def psiTruth (ω : MapConfig P) (P_test : NatMult P → Bool) : HilbertSpaceConfig ω :=
  sorry -- Defined as the convergent sum of (P_test(ω(n)) / n) * e_n

/-- The geometric predicate: The proposition holds under configuration ω iff the vectors are identical -/
def propHolds (ω : MapConfig P) (P_test : NatMult P → Bool) : Prop :=
  psiTruth ω P_test = psiTrue ω
```

*Status:* ✅ — `psiTrue`, `psiTruth` (both `sorry`s above replaced by real definitions with the
proved domination bound `‖coeff n‖² ≤ ‖invIndex n‖²`), and `propHolds` are on disk
(`RandomMap.lean:448–482`).

---

## Phase 6: Calculating the Probability of Truth
Because the proposition's truth is now a property of the mapping $\omega$, we can prove it is a measurable set and calculate its exact probability under our Mehler prior.

```lean
/-- Theorem: The subset of configurations where the proposition holds is Borel measurable -/
theorem measurable_set_propHolds (P_test : NatMult P → Bool) :
    MeasurableSet { ω : MapConfig P | propHolds ω P_test } := by
  sorry -- To be proven using the continuity of the L^2 distance function

/-- The ultimate evaluation: The probability that the proposition is true -/
noncomputable def probabilityOfTruth (P_test : NatMult P → Bool) : Real :=
  (mehlerPrior {ω | propHolds ω P_test}).toReal -- the measure of the truth event
```

*Status:* ✅ on disk — `measurable_set_propHolds` (`RandomMap.lean:504`) and
`probabilityOfTruth` (`:621`, with the truth event spelled correctly as above). Note that the
measurability proof currently rides the Phase 2 discrete placeholder (every set is open, hence
Borel); when ★ work-queue package RM6 installs the pointwise-convergence topology, re-prove it the
intended way — continuity of the L² distance makes `{ψ_truth = ψ_true}` closed. The toy-model
computation (Action Plan item 5) is still open.

---

## Phase 7: Convergence Disintegration (Absolute vs. Conditional)

There is a synergy between this framework and Mathlib that deserves its own phase: **in Mathlib,
unordered summation natively forces unconditional convergence.** `Summable`/`tsum` over an
arbitrary index type are defined via the net of partial sums over finite subsets (`Finset`) — no
order on the index ever enters — and over $\mathbb R$ (indeed any finite-dimensional space)
unconditional convergence coincides with absolute convergence (`summable_norm_iff`,
`Mathlib/Analysis/Normed/Module/FiniteDimension.lean:659`). Since `NatMult P` carries no order
(it is `Multiset P`, the free commutative monoid — do not add one), *any sum that can even be
written over the labels is automatically order-blind, hence absolutely convergent whenever it
exists.* Conditional convergence is not expressible over the labels at all: it can only be
formulated by pulling the family back to the ordered additive clock along a configuration
$\omega$ — at which point it is a property of the random map, i.e. an **event**. This phase
proves the two sides of that disintegration.

### Step 7.1: Absolute Convergence Is Invariant Under Every Map (provable now)

For an absolutely convergent family on the labels, every configuration transports the sum
identically. This is a deterministic, for-all-$\omega$ statement — strictly stronger than
almost-sure, and no measure theory is involved:

```lean
theorem absolute_convergence_invariance
    (c : NatMult P → ℝ) (hc : Summable c) (ω : MapConfig P) :
    Summable (c ∘ ω) ∧ ∑' n, c (ω n) = ∑' m, c m :=
  ⟨(Equiv.summable_iff ω).mpr hc, Equiv.tsum_eq ω c⟩
```

The two lemmas are pinned in the vendored Mathlib: `Equiv.summable_iff (e : γ ≃ β) :
Summable (f ∘ e) ↔ Summable f` and `Equiv.tsum_eq (e : γ ≃ β) (f : β → α) :
∑' c, f (e c) = ∑' b, f b`, the `to_additive` siblings of `Equiv.multipliable_iff` /
`Equiv.tprod_eq` (`Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:175`, `:525`). Note the names
— they are *not* `Summable.equiv` / `tsum_eq_tsum_of_equiv`; those do not exist in this
checkout. Holding for all $\omega$, the identity holds in particular `mehlerPrior`-almost
surely.

*Status:* ✅ — proved on disk exactly as displayed (`RandomMap.lean:661`), with no order ever
introduced on `NatMult P`.

### Step 7.2: Conditional Convergence Is a Null Event (one external input)

Sequential summation needs an enumeration of the clock. `NatAdd.toNat` is already on disk
(`RandomMap.lean:101`); add its inverse and the convergence event:

```lean
/-- Enumeration of the clock: the inverse of `NatAdd.toNat`. -/
def NatAdd.ofNat : ℕ → NatAdd
  | 0 => .zero
  | n + 1 => .succ (ofNat n)

/-- The event that the clock-ordered partial sums of `c ∘ ω` converge. -/
def ConvergentMaps (c : NatMult P → ℝ) : Set (MapConfig P) :=
  { ω | ∃ L : ℝ,
      Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, c (ω (NatAdd.ofNat i)))
        Filter.atTop (nhds L) }

/-- If `c` is not absolutely summable, an exchangeable prior gives the
    clock-ordered convergence event measure zero. -/
theorem conditional_convergence_is_null
    (hμ_exch : ∀ σ : Equiv.Perm NatAdd, {σ moves only finitely many ticks} →
      MeasurePreserving (fun ω : MapConfig P => (σ : NatAdd ≃ NatAdd).trans ω) μ μ)
    (c : NatMult P → ℝ) (hc_not : ¬ Summable c) :
    μ (ConvergentMaps c) = 0 := sorry
```

**An honesty caveat that shapes the statement.** For an *arbitrary* probability measure $\mu$
the theorem is false: by Riemann's rearrangement theorem a non-absolutely-convergent (real,
null) family admits orderings summing to any prescribed value, and a Dirac prior concentrated on
one such ordering gives `ConvergentMaps` measure $1$. The null-set claim is a property of the
*prior*, not of bijections — hence the exchangeability hypothesis `hμ_exch` (invariance of $\mu$
under precomposition with every finitely-supported permutation of the clock). *(Correction,
2026-07-08 — see **RM4**: no countably-additive probability measure on the bijections satisfies
this hypothesis in full, so the on-disk theorem, while true, is vacuously satisfiable only. The
non-vacuous replacements are **RM9d** — a provable Kolmogorov zero–one dichotomy for the
block-shuffle prior, no external input — and **RM8d** — the Kakutani-strength null statement
for the Fisher–Yates prior, with RM8c quasi-invariance standing in for the impossible
exchangeability. RM9e proves the boundary between them: local shuffles genuinely cannot reach
the Kakutani conclusion.)*

Proof architecture, in three layers:

1.  **Measurability of `ConvergentMaps`.** Rewrite the event as a countable
    intersection/union over rational $\epsilon$ and clock bounds $N, M$ of conditions each
    depending on finitely many coordinates of $\omega$ (cylinder events) — the Cauchy criterion
    in the sorted form of Step 4.1, `Finset.range`-bounded throughout. This is routine once the
    intended pointwise-convergence Polish topology from Action Plan item 2 replaces the on-disk
    discrete placeholder (`RandomMap.lean:356`).
2.  **Zero–one dichotomy.** A finitely-supported permutation of the clock changes only finitely
    many partial sums, so `ConvergentMaps` is invariant under the `hμ_exch` action: it is an
    exchangeable event, and the Hewitt–Savage zero–one law forces
    $\mu(\text{ConvergentMaps}) \in \{0, 1\}$. (If Hewitt–Savage is not available in the
    vendored Mathlib, fold this layer into the named external input of layer 3 rather than
    formalizing it from scratch.)
3.  **The lone deep input: ruling out $1$.** That a *randomly* rearranged
    non-absolutely-convergent series diverges almost surely is the classical
    random-rearrangement phenomenon (Kakutani's problem; Dvoretzky-style results). Record it as
    a named, docstring-cited theorem with a `sorry` body —
    `theorem random_rearrangement_divergence … := sorry` — exactly the practice used for
    `bagchi_universality` elsewhere in this repo: one honest, clearly-labeled external citation,
    with everything around it proved.

*Status (2026-07-08):* the statement layer is ✅ done — `NatAdd.ofNat`/`toNat_ofNat`
(`RandomMap.lean:633`), `ConvergentMaps` (`:649`), `measurable_set_ConvergentMaps` (`:673`,
currently via the discrete placeholder), and `conditional_convergence_is_null` stated with the
honest `hμ_exch` hypothesis and closed (`:727`) by delegation to the named, docstring-cited
external input `random_rearrangement_divergence` (`:703`, the file's one `sorry`), which folds
the Hewitt–Savage dichotomy and Kakutani's divergence into a single citation per the layer-2
fallback above (Hewitt–Savage is indeed absent from the vendored Mathlib). The honest residue:
as delegated today, the citation's statement *coincides* with the theorem's, so 7.2 is currently
all citation — and by **RM4** its hypothesis is unsatisfiable anyway. The productive
replacements are queued: **RM9d** (block-shuffle dichotomy, provable with zero external input
via Mathlib's Kolmogorov zero–one law) and **RM8d** (Fisher–Yates prior + quasi-invariance,
with the external input narrowed to the named Kakutani-strength divergence statement).

---

## Phase 8: Strategy B — Sampled Scalars (compatible with, not rival to, Phases 1–7)

Phases 1–7 realize the scalars *deterministically*: `realize` names one real per label, and
Step 4.1 keeps the analysis Gödel-safe with the sorted Cauchy condition — the "$\forall M$
trick", one deterministic sequence, vector indices bounded by a clock variable. There is a
second strategy, the same gesture already made for the Beurling primes but applied to a larger
class of probability distributions: **sample the scalars instead of naming them**.

What is given up: certainty about the exact sequence of reals — the sequence is known only
through approximation (finitely many samples, to finite precision). What is bought: PA is
avoided *without* relying on the sorted-$M$ bookkeeping for safety, because no deterministic
sequence of reals is ever asserted — there is nothing for an induction schema to grab. Where
Strategy A says "for every clock bound $M$, check the finite tuple $(x_1,\dots,x_M) \in
\mathbb R^M$", Strategy B says "draw $M$ samples from the law" — each stage is a finite tuple
of Tarski reals either way, and the one unbounded quantifier (how many samples) still ranges
over the clock sort. The Step 4.1 shield is inherited unchanged; the two strategies are two
readings of the same multi-sorted mechanism.

What is *defined* changes type: not one Cauchy sequence per completed object, but a **set of
Cauchy sequences carrying one probability measure** — the workspace is a Borel probability law
on sequence space (a Polish space again, so the Phase 2/3 machinery is reused verbatim), and
the completed object is approached in probability rather than pointwise.

The payoff is exactly the Phase 7 disintegration, which is the shared interface making the two
strategies mutually compatible: the random map from the naturals (the clock) to the sampled
Tarski reals **conserves** order-blind sums — Step 7.1 holds deterministically for *every*
$\omega$, hence almost surely under any sampling law — and **invalidates** order-dependent
sums — Step 7.2's null-event statement is one that only Strategy B can even express, being a
probability over configurations. (The same i.i.d.-sampling gesture drives the `RcpEuler`
route's multiplicative $X_p$; the two developments may share vocabulary but neither depends on
the other.)

### Step 8.1: Almost-sure multiplicative independence (the sampled `hp_indep`)

For scalars drawn i.i.d. from any atomless law supported in $(1,\infty)$, multiplicative
independence holds almost surely: each fixed nontrivial rational relation
$\sum_i r_i \log x_i = 0$ confines the sample to a null event (conditionally on the other
coordinates, one coordinate must land on a single point of an atomless distribution — Fubini),
and there are only countably many candidate relations. Deliverable (schematic hypotheses in
braces, as in Step 7.2):

```lean
theorem ae_log_linearIndependent
    (μ : Measure (ℕ → ℝ)) [IsProbabilityMeasure μ]
    (hμ : {μ is i.i.d. with atomless marginal supported in (1,∞)}) :
    ∀ᵐ x ∂μ, LinearIndependent ℚ (fun i => Real.log (x i))
```

Corollary, by feeding the a.s. witness to `realize_injective`: **unique factorization is an
almost-sure theorem** of the sampled labels — the Strategy-B counterpart of
`log_primes_linearIndependent`, which proved the same conclusion with probability replaced by
the fundamental theorem of arithmetic. The two results bracket `hp_indep` from both sides:
FTA discharges it exactly for the genuine primes; sampling discharges it a.s. for generic ones.

### Step 8.2: The M-samples reading of completeness (documentation discipline)

Record, in the same docstrings as Action Plan item 7, the Strategy-B reading: replacing the
sorted $\forall M$ bound by $M$ samples from the law leaves every finite stage a point of
$\mathbb R^M$ and keeps the unbounded quantifier on the clock; the completed workspace is a
probability measure on Cauchy sequences rather than a single one. Like item 7, this is a
docstring obligation, not a new proof.

### Step 8.3: The conservation/invalidation pair over the sampled map

Package, as two corollaries of 7.1/7.2 once RM6 and RM9 land (see Action Plan item 12), the headline pair for
the random map from the clock to the sampled Tarski reals: `Summable c` ⟹ the sum is conserved
(for every $\omega$, a fortiori a.s.), and `¬ Summable c` ⟹ clock-ordered convergence is a
null event. Both are one-line consequences of `absolute_convergence_invariance` and
`conditional_convergence_is_null`; their value is the packaging — the compatibility of the two
strategies, stated as theorems.

---

## Action Plan for the Lean 4 Specialist

1.  **Axiomatic Hygiene:** Do not import `Mathlib.SetTheory.ZFC` or any non-constructive choice axioms unless strictly necessary. Keep the background logic restricted to the constructive, dependent type theory of Lean 4. *(Standing discipline. The file currently opens with `import Mathlib`; when convenient, trim to the module imports listed per phase — the theorems' own axiom footprints stay Mathlib's standard trio either way.)*
2.  **Verify Polish Space Properties:** *(OPEN — discrete placeholders on disk, see ★ item 1.)* Prove that `MapConfig` is a Polish space (separable, completely metrizable). This is essential for ensuring that the Borel measure `mehlerPrior` is well-behaved and countably additive without needing the Axiom of Choice.
3.  **Construct the Prior:** *(OPEN — Dirac-sum stub with 3 `admit`s on disk, see ★ item 2.)* Define `mehlerPrior` explicitly. Since `MapConfig` is homeomorphic to a closed subspace of $\mathbb{N}^\mathbb{N}$ (the Baire space), the specialist should construct the measure using the standard product measure on the Baire space and then restrict it to the bijective mappings.
4.  **Prove $L^2$ Convergence:** *(✅ DONE — `summable_invIndex_sq`, the `psiTruth` domination bound, and both `lp` memberships are proved on disk.)* Provide the explicit proof that $\sum \frac{1}{n^2}$ and $\sum \frac{P(\omega(n))^2}{n^2}$ are Cauchy sequences. Use Mathlib's `lp` space theorems to show that `psiTrue` and `psiTruth` are valid, completed elements of the Hilbert space.
5.  **Calculate a Toy Model:** *(OPEN.)* To verify the code compiles and runs, have the specialist compute `probabilityOfTruth` for a trivial, finite toy model (e.g., $P = \{2, 3\}$, where the probability evaluates to a rational fraction like $0.5$). This ensures the measure theory and the metric geometry are perfectly aligned.
6.  **Record, Don't Formalize, the External Shield:** *(✅ DONE in full, 2026-07-08 — both `realize_injective` and `log_primes_linearIndependent` are proved on disk; the metamathematical shield stays prose, exactly as prescribed.)* The safety argument in Step 1.3 (Julia Robinson's theorem's dependence on the standard integers' uniform $+1$ gap; Tarski's quantifier-elimination undefinability of infinite discrete subsets of $\mathbb R$) is a metamathematical justification for the design, not itself a Lean deliverable — do not attempt to formalize Robinson's or Tarski's theorems. The one concrete consequence that *is* checkable and should be proved is `Function.Injective (realize p)` given `hp_indep`, confirming that unique factorization survives the real-valued realization. For the genuine-primes instantiation (see the Remark closing Step 1.3), additionally prove `log_primes_linearIndependent` via the `Nat.factorizationEquiv` pins there, which discharges `hp_indep` and makes `realize_injective` unconditional.
7.  **Keep the Cauchy Quantifiers Sorted:** *(Standing discipline — the on-disk convergence lemmas already have the `Finset`-indexed shape; keep extending the docstrings as new lemmas land.)* When discharging item 4, phrase (and, in docstrings, record) all convergence and completeness facts through `Finset`-indexed partial sums, per Step 4.1: the only unbounded quantifier ranges over the index sort (`NatAdd`), and the scalar side only ever compares finite tuples in $\mathbb R^M$. Mathlib's `Summable`/`CauchySeq`/`lp` API already has this shape, so this is a documentation discipline, not a proof obligation — a docstring on the convergence lemmas noting the sorted form (bounded vector indices, unbounded quantifier on the clock) suffices. Include the two Step 4.1 precisions in the same docstrings: the condition is deliberately *multi-sorted*, not a first-order RCF formula (that is why Tarski decidability is untouched), and the continuum itself emerges from the completion (Mathlib's `Real` is already the Cauchy completion of $\mathbb Q$, not a postulate).
8.  **Prove Step 7.1 as stated:** *(✅ DONE — proved on disk exactly as prescribed.)* `absolute_convergence_invariance` closes with the two pinned lemmas `Equiv.summable_iff` and `Equiv.tsum_eq` — zero external input, and do not introduce any order on `NatMult P` while doing it (Mathlib's unordered `tsum` doing the work is the point).
9.  **Formalize Step 7.2 with the honest hypothesis:** *(PARTIAL, 2026-07-08 — the statement, the `hμ_exch` hypothesis, `measurable_set_ConvergentMaps`, and the folded citation are all on disk; by RM4 the hypothesis is unsatisfiable, so the open residue is the RM9d/RM8d replacement pair plus the non-trivial measurability re-proof once RM6's topology lands.)* State `conditional_convergence_is_null` with the exchangeability hypothesis on the prior (to be discharged for `mehlerPrior` once item 3 lands); prove measurability of `ConvergentMaps` via `Finset.range`-bounded Cauchy conditions on cylinder events (item 2 topology, item 7 discipline); and record the lone deep input as the named, docstring-cited external theorem `random_rearrangement_divergence` (Kakutani's problem on random rearrangements) with a `sorry` body — the same citation practice as `bagchi_universality`. If the Hewitt–Savage zero–one law is missing from the vendored Mathlib, fold the dichotomy into that same named input rather than formalizing it from scratch.
10. **Prove Step 8.1 (`ae_log_linearIndependent`):** express the failure of ℚ-linear independence as the countable union, over nonzero finitely-supported `q : ℕ →₀ ℚ`, of the relation events `{x | ∑ i ∈ q.support, q i • Real.log (x i) = 0}`; show each is null by conditioning on all but one coordinate (Fubini on the product law) and applying atomlessness of the remaining marginal; conclude a.s. linear independence and derive the a.s.-unique-factorization corollary through `realize_injective`.
11. **Record Step 8.2:** add the Strategy-B (M-samples) reading to the same docstrings item 7 maintains — one paragraph per convergence lemma noting that the sorted `∀ M` bound and the `M`-sample draw are the same multi-sorted mechanism, deterministic vs. in-probability.
12. **Package Step 8.3:** once RM6 and RM9 land, state the conservation corollary (from `absolute_convergence_invariance`) and the invalidation-side corollary (RM9d's dichotomy, upgraded to the null statement by RM8d where it applies) side by side, as the formal compatibility statement of Strategies A and B.