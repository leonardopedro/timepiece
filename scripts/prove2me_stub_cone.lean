/-
For every converted prove2.me solution theorem (`Prove2me.Solution.*`), list the declarations in
its dependency cone whose own proof is `sorry`, together with their modules.  In the converted
library these are exactly the platform statement stubs `Theorems.Thm_*` (platform design: a
`Thm_` module states a theorem; its proof is a separate accepted submission, not part of the
download).  Output lines: `<solution> :: <decl> @ <module> ; ...`; solutions with an empty cone
are omitted.

Run after `lake build Prove2me`:
    lake env lean scripts/prove2me_stub_cone.lean > converted/stub_dependencies.txt
-/
import Prove2me
open Lean

partial def sorryCone (env : Environment) (n : Name) (seen : IO.Ref NameSet)
    (out : IO.Ref NameSet) : IO Unit := do
  if (← seen.get).contains n then return
  seen.modify (·.insert n)
  let some ci := env.find? n | return
  let consts := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])
  if consts.contains ``sorryAx then out.modify (·.insert n)
  for c in consts do sorryCone env c seen out

#eval show CoreM Unit from do
  let env ← getEnv
  let sols := env.constants.toList.filterMap fun (n, _) =>
    if (`Prove2me.Solution).isPrefixOf n && !n.isInternalDetail then some n else none
  for s in sols.toArray.qsort (·.toString < ·.toString) do
    let seen ← IO.mkRef ({} : NameSet)
    let out ← IO.mkRef ({} : NameSet)
    sorryCone env s seen out
    let ds := (← out.get).toList.map fun n =>
      s!"{n} @ {(env.getModuleIdxFor? n).map (env.header.moduleNames[·]!) |>.getD `none}"
    unless ds.isEmpty do
      IO.println s!"{s} :: {" ; ".intercalate (ds.toArray.qsort (· < ·)).toList}"
