import VersoManual
import Book

open Verso.Genre Manual

def config : Config where
  emitTeX := false
  emitHtmlSingle := .immediately
  emitHtmlMulti := .no
  htmlDepth := 2

def main := manualMain (%doc Book) (config := { config with })
