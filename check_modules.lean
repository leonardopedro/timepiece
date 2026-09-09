import RiemannProof
open Lean
run_meta do
  let env ← getEnv
  IO.println s!"Total modules: {env.header.moduleNames.size}"
  let mut count := 0
  for m in env.header.moduleNames do
    IO.println m
    count := count + 1
  IO.println s!"Count: {count}"
