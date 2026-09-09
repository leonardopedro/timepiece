import VersoManual

open Verso.Genre Manual

#doc (Manual) "Trivial Test Chapter" =>
%%%
tag := "trivial-test"
%%%

# Hello

This is a trivial chapter used only to test the section-count threshold. It is
deliberately not included in `Book.lean`: it is kept as the minimal
reproducer for the Verso section-count behaviour that the repository's Verso
patches address, so that the patches can be re-derived if a future toolchain
changes that behaviour.
