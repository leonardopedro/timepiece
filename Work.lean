/-
# `Work` library root

Deliberately empty aggregator.  New developments live in `Work/<Name>.lean` and
import only the specific `BookProof.*` chapters they depend on, so that building
`Work.<Name>` compiles the minimal cone of modules.  This root is not a default
target and imports nothing, so `lake build Work` is free.
-/
