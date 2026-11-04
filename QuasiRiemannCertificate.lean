/-!
QuasiRiemannCertificate — the quasi-Riemann hypothesis (zero-free half-plane
`7/8 < Re s`) as closed certificates for the Lean 4 → nanoda → MM0 pipeline
(`australVM/scripts/lean2mm0`; `australVM/docs/lean4mm0.md`).

# Scope — read this first

The *analytic* proof — that `riemannZeta s ≠ 0` for every `s` with `7/8 < s.re`,
the theorem `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` — lives in
`math/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean` (Mathlib-based, the
~2,900-file `DirichletL` tree; the alternate 11/12 preprint has no Lean
formalization, so the 7/8 development is the only Lean4 version of the result).
That development is far beyond this pipeline in size, and its proof terms are
analytic, not ground-Bool reductions: `lean2mm0` converts exactly theorems of
the form `x = true` over closed Boolean computations, and `docs/lean4mm0.md`
§9.2 records that carrying non-Boolean analytic proofs would need a different,
much larger target theory.

So what this file is — the prototype the conversion request asked for:

* the **statement of record**, restated over opaque stand-ins (no Mathlib) so
  it survives into the export and is type-checked by nanoda. It is *asserted*
  here, not proved: the proof is the OAI development above.
* the **arithmetic skeleton of the statement** as nine `rfl`-closed
  certificates over scaled naturals: the bound θ = 7/8 read exactly, θ < 1 (the
  "quasi" in quasi-Riemann), the ε = 1/8 gap, the in/out-of-half-plane boundary
  at 10⁻⁴, and the pole at s = 1 that the Dirichlet statement excludes
  separately (`hpole : ¬ (χ = 1 ∧ s = 1)` in `Nonvanishing.lean`).

# Discipline (same as GapCertificate/Layout)

* **no imports** — pure core Lean: compiles standalone, the export needs no
  Mathlib.
* every certificate is a **closed Bool expression** closed by kernel
  reduction (`rfl` / `Eq.refl`). No `native_decide`/`decide` — those emit
  `Lean.ofReduceBool` / `_nativeDecide_*` terms that the independent external
  checker nanoda (via the `lean4export` NDJSON pipeline) cannot reduce.
* decimals are read exactly as (mantissa, exponent) pairs — no `Float`
  anywhere — and all arithmetic is carried on the common denominator `10⁴`
  as scaled naturals, exactly as `GapCertificate.lean` does.

# Regenerate the pinned fixture in unfer

Matching toolchain (Lean 4.28.0), official lean4export 3.1.0 backport
revision `d065b00` — the same tool that produced the pinned S31 fixtures:

  lean -o QuasiRiemannCertificate.olean QuasiRiemannCertificate.lean
  LEAN_PATH=. lean4export QuasiRiemannCertificate \
    -- QuasiRiemannCertificate.riemannZeta_ne_zero_of_seven_eighths_lt_re \
    -- QuasiRiemannCertificate.read_bound_verified \
    -- QuasiRiemannCertificate.bound_computes_verified \
    -- QuasiRiemannCertificate.bound_is_seven_eighths_verified \
    -- QuasiRiemannCertificate.theta_lt_one_verified \
    -- QuasiRiemannCertificate.epsilon_gap_verified \
    -- QuasiRiemannCertificate.epsilon_is_one_eighth_verified \
    -- QuasiRiemannCertificate.interior_point_verified \
    -- QuasiRiemannCertificate.boundary_point_excluded_verified \
    -- QuasiRiemannCertificate.pole_at_one_verified \
    > ../unfer/prob_kernel/tests/fixtures/quasi_rh_certificate.ndjson
-/

-- ── the bound as scaled-natural arithmetic ──────────────────────────────

-- Powers of ten (the denominators). `10^4 = 10000` is the common
-- denominator: every decimal in the statement is read at 10⁻⁴.
def pow10 : Nat → Nat
  | 0 => 1
  | n + 1 => 10 * pow10 n

def denom : Nat := pow10 4

-- The bound θ = 7/8 read exactly as (mantissa, exponent): 0.8750.
def boundMantissa : Nat := 8750
def boundExp : Nat := 4

-- θ scaled by `denom`, *computed* rather than asserted: 7·10000 / 8 = 8750.
def boundScaled : Nat := 7 * denom / 8

-- The principal pole of a Dirichlet L-function sits at s = 1; the Dirichlet
-- statement excludes it separately (`hpole`), so its real part is recorded
-- as data: Re = 1.0000.
def poleScaled : Nat := 1 * denom

-- ── the statement of record, over opaque stand-ins ──────────────────────
--
-- Mirrors `math/lean/ComparatorChallenges/QuasiRiemannHypothesis.lean`
--   theorem riemannZeta_ne_zero_of_seven_eighths_lt_re
--       {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0
-- with ℂ/ζ/0/`·re` as opaque constants (this file has no imports, so no
-- Mathlib) and the real-part comparison as scaled-natural arithmetic —
-- `7/8 < Re s` reads `8750 < complexReScaled s`, both sides × 10⁴.

/-- Stand-in for ℂ. An `inductive` (one constructor carrying the scaled real
part) rather than an opaque *type*: `opaque x : T` requires `Nonempty T`, and
the deriving clause discharges that. The representation is never used to
decide the statement — `complexReScaled` below is opaque. -/
inductive Complex where
  | mk (reScaled : Nat) : Complex
  deriving Nonempty

-- `noncomputable`: an `opaque` constant with no value is backed by
-- `Classical.ofNonempty` for the compiler; the kernel never unfolds these,
-- which is exactly the point — they are the uninterpreted analytic atoms.
noncomputable opaque complexZero : Complex
noncomputable opaque riemannZeta : Complex → Complex
/-- `Re s` scaled by 10⁴ (scaled-natural representation of the real part). -/
opaque complexReScaled : Complex → Nat

/-- **The quasi-Riemann hypothesis (7/8), statement of record.** Asserted,
not proved here — the proof is
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` in
`math/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean`. -/
def riemannZeta_ne_zero_of_seven_eighths_lt_re : Prop :=
  ∀ s : Complex, boundScaled < complexReScaled s → riemannZeta s ≠ complexZero

-- Certificate 1: the bound reads θ = 0.8750 — mantissa 8750, exponent 4.
def read_bound_checked : Bool := boundMantissa == 8750 && boundExp == 4
theorem read_bound_verified : read_bound_checked = true := by
  rfl

-- Certificate 2: the scaled bound computes to 8750 (7·10⁴ / 8, kernel
-- reduction — not an assertion of the decimal).
def bound_computes_checked : Bool := boundScaled == 8750
theorem bound_computes_verified : bound_computes_checked = true := by
  rfl

-- Certificate 3: the bound *is* seven eighths — cross-multiplied on the
-- common denominator: 7 · 10000 = 8 · 8750.
def bound_is_seven_eighths_checked : Bool := 7 * denom == 8 * boundScaled
theorem bound_is_seven_eighths_verified : bound_is_seven_eighths_checked = true := by
  rfl

-- Certificate 4: θ < 1 — the "quasi" in quasi-Riemann: the half-plane is a
-- *proper* subset of Re s > 0... it is the fixed θ < 1 of docs/003.md:
-- "a fixed zero-free half-plane Re s > θ with θ < 1".
def theta_lt_one_checked : Bool := boundScaled < denom
theorem theta_lt_one_verified : theta_lt_one_checked = true := by
  rfl

-- Certificate 5: the gap below the bound, 1 − θ = 0.1250 (scaled 1250).
def epsilon_gap_checked : Bool := denom - boundScaled == 1250
theorem epsilon_gap_verified : epsilon_gap_checked = true := by
  rfl

-- Certificate 6: the gap is exactly one eighth — (1 − θ) · 8 = 1 — so the
-- zero-free region reaches `1 − 1/8` of the unit line, i.e. ε = 1/8 is the
-- slack the result certifies.
def epsilon_is_one_eighth_checked : Bool := (denom - boundScaled) * 8 == denom
theorem epsilon_is_one_eighth_verified : epsilon_is_one_eighth_checked = true := by
  rfl

-- Certificate 7: σ = 0.9000 (scaled 9000) lies in the half-plane — the
-- statement's hypothesis `θ < Re s` holds at this point.
def interior_point_checked : Bool := boundScaled < 9000
theorem interior_point_verified : interior_point_checked = true := by
  rfl

-- Certificate 8: σ = 0.8749 (scaled 8749) lies below the bound — the
-- hypothesis `θ < Re s` fails there, so the boundary is sharp at 10⁻⁴.
def boundary_point_excluded_checked : Bool := 8749 < boundScaled
theorem boundary_point_excluded_verified : boundary_point_excluded_checked = true := by
  rfl

-- Certificate 9: the pole sits *inside* the half-plane — Re(1) = 1.0000 =
-- denom and θ < 1 — which is exactly why the Dirichlet statement carries
-- the separate pole exclusion `hpole : ¬ (χ = 1 ∧ s = 1)`.
def pole_at_one_checked : Bool := poleScaled == denom && boundScaled < poleScaled
theorem pole_at_one_verified : pole_at_one_checked = true := by
  rfl
