/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle
-/
import Lean

/-!
# A memoized `#print axioms`

`#print axioms c` collects the transitive axiom set of `c` with `Lean.collectAxioms`, which
starts a fresh `visited` set for **every** call.  A file that audits hundreds or thousands of
related declarations therefore re-walks their shared dependency closure once per declaration;
for `ChapterRoadmapAudit` (2133 audits whose closures are almost entirely shared Mathlib) that
was 1520 s of pure repetition in one module.

Memoisation alone does not fix the wall clock, because the cache lives in *one* module: it is
warm after the first audit and useless to the second core.  So the ledger is also *sliced* —
`ChapterRoadmapAuditPart1`–`Part8` hold the same 2133 directives, verbatim and in the original
order, and `ChapterRoadmapAudit` imports them, which lets Lake elaborate eight modules in
parallel.  Measure: 1520 s (one module) before, 20.4 s wall (eight slices of 250–290 directives
plus the aggregate) after, with the audited name list unchanged — see the 2026-11-13n entry in
`CONSOLIDATED_PLAN.md` for the check.

`#audit_axioms c` prints the same line — `'c' depends on axioms: [...]` — but memoizes the axiom
set of every constant it visits in an environment extension, so each constant is traversed at
most once across the whole file.  The output has the semantics of `#print axioms`: `sorryAx`
appears in the list when a declaration depends on a `sorry`, and the list is sorted.

The cache stores `NameSet`s rather than raw axiom lists: the axiom set of a constant is a few
names, so a cache entry is tiny, whereas threading un-deduplicated lists through the whole
closure of Mathlib would need gigabytes.
-/

open Lean Elab Command

namespace BookProof.AxiomAudit

/-- Cache of transitive axiom sets, threaded through the environment so that consecutive
`#audit_axioms` commands reuse each other's work. -/
initialize axiomsCache : EnvExtension (NameMap NameSet) ←
  registerEnvExtension (pure {})

mutual

/-- Memoized transitive axiom collection for a constant.  The cache is threaded explicitly; a
constant is looked up before its value is traversed and stored with its final axiom set, so the
whole file traverses each constant at most once.  `visited` only breaks cycles in the value
graph. -/
partial def constAxioms (env : Environment) (visited : NameSet) (cache : NameMap NameSet)
    (c : Name) : NameMap NameSet × NameSet :=
  match cache.find? c with
  | some ax => (cache, ax)
  | none =>
    if visited.contains c then (cache, {})
    else
      let visited := visited.insert c
      match env.checked.get.find? c with
      | some (.axiomInfo v) =>
        let (cache, a) := exprAxioms env visited cache v.type
        let ax := a.insert c
        (cache.insert c ax, ax)
      | some (.defnInfo v) =>
        let (cache, a1) := exprAxioms env visited cache v.type
        let (cache, a2) := exprAxioms env visited cache v.value
        let ax := a1.union a2
        (cache.insert c ax, ax)
      | some (.thmInfo v) =>
        let (cache, a1) := exprAxioms env visited cache v.type
        let (cache, a2) := exprAxioms env visited cache v.value
        let ax := a1.union a2
        (cache.insert c ax, ax)
      | some (.opaqueInfo v) =>
        let (cache, a1) := exprAxioms env visited cache v.type
        let (cache, a2) := exprAxioms env visited cache v.value
        let ax := a1.union a2
        (cache.insert c ax, ax)
      | some (.quotInfo _) => (cache.insert c {}, {})
      | some (.ctorInfo v) =>
        let (cache, ax) := exprAxioms env visited cache v.type
        (cache.insert c ax, ax)
      | some (.recInfo v) =>
        let (cache, ax) := exprAxioms env visited cache v.type
        (cache.insert c ax, ax)
      | some (.inductInfo v) =>
        let (cache, a) := exprAxioms env visited cache v.type
        let rec goCtors (ctors : List Name) (cache : NameMap NameSet) (acc : NameSet) :
            NameMap NameSet × NameSet :=
          match ctors with
          | [] => (cache, acc)
          | k :: ks =>
            let (cache, ak) := constAxioms env visited cache k
            goCtors ks cache (acc.union ak)
        let (cache, ax) := goCtors v.ctors cache a
        (cache.insert c ax, ax)
      | none => (cache.insert c {}, {})

/-- Axioms of every constant occurring in an expression, with the same threading. -/
partial def exprAxioms (env : Environment) (visited : NameSet) (cache : NameMap NameSet)
    (e : Expr) : NameMap NameSet × NameSet :=
  e.getUsedConstants.toList.foldl (init := (cache, {})) fun (cache, acc) d =>
    let (cache, a) := constAxioms env visited cache d
    (cache, acc.union a)

end

/-- `#audit_axioms c` prints `'c' depends on axioms: [...]`, like `#print axioms`, but reuses a
per-environment cache so auditing many related declarations costs one traversal of their shared
closure rather than one per declaration.  Like the stock command it reports every candidate of an
overloaded name (`realizeGlobalConstWithInfos`), one line each. -/
syntax (name := auditAxiomsCmd) "#audit_axioms" ident : command

elab_rules : command
  | `(#audit_axioms $id:ident) => do
    let cs ← liftCoreM <| realizeGlobalConstWithInfos id
    let env ← getEnv
    let mut cache := axiomsCache.getState env
    for c in cs do
      let (cache', ax) := constAxioms env {} cache c
      cache := cache'
      let names := ax.toList.mergeSort Name.lt
      if names.isEmpty then
        logInfo m!"'{c}' does not depend on any axioms"
      else
        let body := ", ".intercalate (names.map (fun n => n.toString))
        logInfo m!"'{c}' depends on axioms: [{body}]"
    modifyEnv fun e => axiomsCache.modifyState e (fun _ => cache)

end BookProof.AxiomAudit
