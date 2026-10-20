import VersoManual
import ProbGame

open Verso.Genre Manual

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  -- One page per world.
  htmlDepth := 1

def main := manualMain (%doc ProbGame) (config := config)
