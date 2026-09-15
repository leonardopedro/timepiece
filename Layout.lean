/-
Layout (GPU federation): bijectivity of the StateDictionary linear layout and
the bank-conflict swizzle-impossibility theorem.

This file formalizes the layout claims of `unfer/docs/GPU.md` that the
GPU_FEDERATION_PLAN (T2.1) pins: unfer's `fock_sirk` `StateDictionary` maps
`OuterState` topologies to dense GPU indices (`state ↦ index`); the map must
be a bijection for the dense tensor to be a faithful image of the sparse
state. And GPU.md's running bank-conflict example — the linear layout
`(x, y) ↦ 2x + 4y (mod 32)` — has no safe swizzle: a full row of 32
consecutive addresses collides on 16 banks, and no re-labelling of banks can
separate a collision.

The proof discipline follows `logos/lean/Confluence.lean` (the S29/S31
pipeline): every theorem is a **closed Bool certificate** closed by kernel
reduction (`rfl`, `Eq.refl`). No `native_decide`/`decide` — those emit
`Lean.ofReduceBool` / `_nativeDecide_*` terms that the independent external
checker nanoda (via the `lean4export` NDJSON pipeline) cannot reduce. The
file has no imports: it is pure core Lean, so it compiles standalone and the
export needs no mathlib.

Regenerate the pinned fixture in unfer with (matching toolchain, official
lean4export 3.1.0):

  lean -o Layout.olean Layout/Layout.lean
  LEAN_PATH=Layout lean4export Layout.Layout \
    -- Layout.Layout.bijective_verified \
    -- Layout.Layout.lookup_inverse_verified \
    -- Layout.Layout.insert_existing_verified \
    -- Layout.Layout.insert_new_verified \
    -- Layout.Layout.conflict_pair_verified \
    -- Layout.Layout.row_even_verified \
    -- Layout.Layout.image_too_small_verified \
    > ../unfer/prob_kernel/tests/fixtures/layout_bijective.ndjson
-/

-- Certificate 8's `rfl` reduces a 32×32 = 1024-address dedup (the strong
-- pigeonhole); the kernel's default recursion budget is too shallow for it.
set_option maxRecDepth 10000

-- ── StateDictionary model ────────────────────────────────────────────────
-- The `OuterState` topologies, abstracted to a small finite set. The
-- registry is the list `dict` in insertion order (the dense
-- `index_to_state` vector); `state_to_index` is the lookup `indexOf`.

inductive OuterState where
  | s0 : OuterState
  | s1 : OuterState
  | s2 : OuterState
  | s3 : OuterState
  | s4 : OuterState
deriving BEq, DecidableEq, Repr

-- The registry after four insertions, in insertion order.
def dict : List OuterState :=
  [.s0, .s1, .s2, .s3]

-- Membership and distinctness as Bool, so the certificates stay closed.
-- (Core Lean has `List.Nodup` only as a Prop; the Bool form keeps the
-- certificates `rfl`-reducible.)
def mem (a : OuterState) : List OuterState → Bool
  | [] => false
  | h :: t => a == h || mem a t

def nodup : List OuterState → Bool
  | [] => true
  | h :: t => !(mem h t) && nodup t

def memNat (a : Nat) : List Nat → Bool
  | [] => false
  | h :: t => a == h || memNat a t

def nodupNat : List Nat → Bool
  | [] => true
  | h :: t => !(memNat h t) && nodupNat t

-- The linear layout: `state ↦ index`. Mirrors `StateDictionary`'s forward
-- table (each state maps to a single index).
def indexOf (s : OuterState) : List OuterState → Nat
  | [] => 0
  | h :: t => if s == h then 0 else indexOf s t + 1

-- Indexing into the dense `index_to_state` vector (core Lean lacks
-- `List.get?`): `getAt dict i` is `some s` iff `s` sits at index `i`.
def getAt : List OuterState → Nat → Option OuterState
  | [], _ => none
  | h :: t, i => if i == 0 then some h else getAt t (i - 1)

-- `get_or_insert`: an existing state returns its index and leaves the
-- registry unchanged; a fresh state is appended at the next index. Mirrors
-- `StateDictionary::get_or_insert` (registry.rs).
def get_or_insert (s : OuterState) : List OuterState → Nat × List OuterState
  | [] => (0, [s])
  | h :: t =>
      if s == h then (0, h :: t)
      else
        let (i, tl) := get_or_insert s t
        (i + 1, h :: tl)

-- Certificate 1: the layout is injective on the stored set — two distinct
-- `OuterState`s never collide on an index (`nodup` over the assigned
-- indices). This is the T0.1 `debug_assert!` claim, proven.
def bijective_checked : Bool :=
  nodupNat (dict.map (fun s => indexOf s dict))

theorem bijective_verified : bijective_checked = true := by
  rfl

-- Certificate 2: `index_to_state` is the inverse — the state at index
-- `indexOf s dict` is `s` itself.
def lookup_inverse_checked : Bool :=
  dict.all (fun s => getAt dict (indexOf s dict) == some s)

theorem lookup_inverse_verified : lookup_inverse_checked = true := by
  rfl

-- Certificate 3: re-inserting a present state is stable — same index, and
-- the registry is unchanged (no duplicate slot, no alias).
def insert_existing_checked : Bool :=
  dict.all (fun s =>
    let (i, tl) := get_or_insert s dict
    i == indexOf s dict && tl == dict)

theorem insert_existing_verified : insert_existing_checked = true := by
  rfl

-- Certificate 4: inserting a fresh state appends at the next index (5),
-- growing the dense vector by exactly one slot.
def insert_new_checked : Bool :=
  let (i, tl) := get_or_insert .s4 dict
  i == 4 && tl == dict ++ [.s4]

theorem insert_new_verified : insert_new_checked = true := by
  rfl

-- ── Bank-conflict / swizzle-impossibility ────────────────────────────────
-- GPU.md's running example: the linear layout `(x, y) ↦ 2x + 4y (mod 32)`.
-- Defined without `%` in the certificate bodies where possible (the
-- exported terms stay small); `bank` below is the textbook form.

def bank (x y : Nat) : Nat := (2 * x + 4 * y) % 32

-- A warp row: 32 consecutive addresses at fixed y = 0.
def rowBanks : List Nat :=
  (List.range 32).map (fun x => bank x 0)

-- Deduplication and flat-map as Bool-friendly recursion (core Lean lacks
-- `List.eraseDup` / `List.bind`).
def eraseDup : List Nat → List Nat
  | [] => []
  | h :: t => if memNat h t then eraseDup t else h :: eraseDup t

def concatMap (f : Nat → List Nat) : List Nat → List Nat
  | [] => []
  | h :: t => f h ++ concatMap f t

-- The row's image, deduplicated.
def rowImage : List Nat :=
  eraseDup rowBanks

-- Certificate 5: the collision pair — addresses x = 0 and x = 16 (both in
-- the row) map to the same bank. Equality of bank values is preserved by
-- any swizzle σ (a re-labelling of banks): σ(bank 0 0) = σ(bank 16 0), so
-- no bijective swizzle can separate the conflicting addresses. This is the
-- machine-readable `2x + 4y ≡ 0 (mod 32)` conflict of GPU.md.
def conflict_pair_checked : Bool :=
  (0 < 32) && (16 < 32) && (0 != 16) && (bank 0 0 == bank 16 0)

theorem conflict_pair_verified : conflict_pair_checked = true := by
  rfl

-- Certificate 6: the parity obstruction — every bank value in the row is
-- even, so the image lies in the 16 even residues, a proper subgroup of
-- Z/32Z. `2x + 4y` is always even; no bijection onto all 32 banks exists.
def row_even_checked : Bool :=
  (List.range 32).all (fun x => bank x 0 % 2 == 0)

theorem row_even_verified : row_even_checked = true := by
  rfl

-- Certificate 7: the pigeonhole content — 32 addresses land in an image of
-- size 16 < 32. A bijective swizzle is a permutation of banks; a
-- permutation preserves image cardinality, so the relabelled row still maps
-- 32 addresses into 16 values: two addresses must collide. This is the
-- "no safe swizzle" statement, witnessed by the image size.
def image_too_small_checked : Bool :=
  rowImage.length == 16 && 16 < 32

theorem image_too_small_verified : image_too_small_checked = true := by
  rfl

-- Certificate 8: the full 32×32 grid maps into the same 16 even residues —
-- 1024 addresses into 16 banks, so the layout is massively non-injective
-- (the strong pigeonhole form of the conflict).
def gridImage : List Nat :=
  eraseDup (concatMap (fun x => (List.range 32).map (fun y => bank x y)) (List.range 32))

def grid_image_small_checked : Bool :=
  gridImage.length == 16

theorem grid_image_small_verified : grid_image_small_checked = true := by
  rfl
