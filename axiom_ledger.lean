/-
Per-declaration axiom ledger: for every theorem in the imported module cone,
write `name <TAB> axiom,axiom,...` to a TSV file, so the axiom set of each
declaration is data that can be diffed across commits instead of a pass/fail
log line.

`axiom_gate.lean` already computes the same transitive closure and prints
`BAD` for anything outside {propext, Classical.choice, Quot.sound}.  Its output
is a run log: it answers "is the tree clean *now*", not "did the axiom set of
*this* declaration change".  This file is the second question.  The whitelist
check lives in `scripts/axiom-audit`, which runs this ledger and diffs it.

Coverage is the import cone below, exactly as for `axiom_gate.lean`: a module is
gated if it is imported here AND its name starts with one of the gated
prefixes.  Widening the audit means adding imports, not editing the walk.

Run:  lake env lean axiom_ledger.lean           (writes evidence/axiom-ledger.tsv)
      AXIOM_LEDGER_OUT=path lake env lean axiom_ledger.lean
-/
import Mathlib
import BookProof.ChapterBRSTNilpotent
import BookProof.ChapterNavierStokes
import BookProof.ChapterGaugeFixing
import BookProof.ChapterMassGap
import BookProof.ChapterGhostField
import BookProof.FieldStrength.ChapterYangMillsFieldStrength
import BookProof.Sirk.ChapterSirkFinitePrecision

open Lean

/-- The folders the ledger covers.  `Book.` is deliberately excluded (prose
chapters, user rule: never publish from `Book/`). -/
def gateModule (m : Name) : Bool :=
  let s := m.toString
  s.startsWith "BookProof." || s.startsWith "PnpProof." || s.startsWith "UsedRoute."
    || s.startsWith "UnusedRoute." || s.startsWith "RandomMap."

/-- The axioms a declaration may depend on.  `sorryAx` is not in the list, so a
`sorry` shows up in the ledger as a foreign axiom rather than as a separate
finding. -/
def allowedAxiom (n : Name) : Bool :=
  n == `propext || n == `Classical.choice || n == `Quot.sound

run_meta do
  let env ← getEnv
  let modNames := env.header.moduleNames
  let getMod : Name → Option Name := fun n =>
    match env.getModuleIdxFor? n with
    | some idx => modNames[idx.toNat]?
    | none => none
  -- Iterative DFS with a memo, same shape as `axiom_gate.lean`: a `let rec`
  -- inside `Id.run` trips Lean v4.28's evaluator sorry-guard.
  let axiomsOf (seed : Name) (memo : Std.HashMap Name (List Name)) : List Name := Id.run do
    let mut acc : Std.HashSet Name := {}
    let mut done : Std.HashSet Name := {}
    let mut work := [seed]
    while !work.isEmpty do
      let u := work.head!
      work := work.tail!
      if done.contains u then continue
      done := done.insert u
      match memo.get? u with
      | some axu => acc := acc.union (Std.HashSet.ofList axu)
      | none =>
        match env.find? u with
        | some (.axiomInfo _) => acc := acc.insert u
        | some (.thmInfo t) =>
            work := t.type.getUsedConstants.toList ++ t.value.getUsedConstants.toList ++ work
        | some (.defnInfo d) =>
            work := d.type.getUsedConstants.toList ++ d.value.getUsedConstants.toList ++ work
        | some (.opaqueInfo o) =>
            work := o.type.getUsedConstants.toList ++ o.value.getUsedConstants.toList ++ work
        | _ => pure ()
    acc.toList.mergeSort (fun a b => a.toString < b.toString)
  let gated :=
    (env.constants.toList.filter fun (n, _) =>
        match getMod n with | some m => gateModule m | none => false).filter fun (_, ci) =>
      match ci with | .thmInfo _ => true | _ => false
  let acc0 : Std.HashMap Name (List Name) × List (Name × List Name) := ({}, [])
  let (_, pairs) := gated.foldl
    (fun acc nci =>
      let memo := acc.1
      let out := acc.2
      let n := nci.1
      let ax := axiomsOf n memo
      (memo.insert n ax, out ++ [(n, ax)]))
    acc0
  -- One row per declaration, name first, axioms after a tab.  A clean
  -- declaration gets an empty second field, so the file has one line per
  -- theorem regardless of its footprint and a diff is a line-for-line change.
  let rows := pairs.map fun (n, ax) =>
    let userName := ((privateToUserName? n).getD n).toString
    s!"{userName}\t{",".intercalate (ax.map (·.toString))}"
  let nDecl := pairs.length
  let nForeign := pairs.foldl (fun k (_, ax) => k + if ax.all allowedAxiom then 0 else 1) 0
  let body := String.intercalate "\n" rows ++ "\n"
  let target ← match ← IO.getEnv "AXIOM_LEDGER_OUT" with
    | some p => pure p
    | none => pure "evidence/axiom-ledger.tsv"
  let path : System.FilePath := target
  if let some dir := path.parent then
    IO.FS.createDirAll dir
  IO.FS.writeFile path body
  logInfo s!"LEDGER: wrote {nDecl} declarations to {path}"
  logInfo s!"LEDGER: {nForeign} with axioms outside the allowed three"
