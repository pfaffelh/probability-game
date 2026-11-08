import VersoManual
import ProbGame

open Verso.Genre Manual
open Verso.Output Html

-- The icon of the browser tab: a die (an SVG, inline as a data URL)
def favicon : String :=
  "data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCA2NCA2NCI+PHJlY3QgeD0iNCIgeT0iNCIgd2lkdGg9IjU2IiBoZWlnaHQ9IjU2IiByeD0iMTIiIGZpbGw9IiNmZGZhZjMiIHN0cm9rZT0iIzJiM2E1NSIgc3Ryb2tlLXdpZHRoPSI0Ii8+PGcgZmlsbD0iIzJiM2E1NSI+PGNpcmNsZSBjeD0iMTkiIGN5PSIxOSIgcj0iNiIvPjxjaXJjbGUgY3g9IjQ1IiBjeT0iMTkiIHI9IjYiLz48Y2lyY2xlIGN4PSIzMiIgY3k9IjMyIiByPSI2Ii8+PGNpcmNsZSBjeD0iMTkiIGN5PSI0NSIgcj0iNiIvPjxjaXJjbGUgY3g9IjQ1IiBjeT0iNDUiIHI9IjYiLz48L2c+PC9zdmc+Cg=="

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  -- One page per world.
  htmlDepth := 1
  -- the edition of the game, for `game.js` (see `ProbGame.edition`)
  extraHead := #[{{<link rel="icon" type="image/svg+xml" href={{favicon}}/>}}, {{<meta name="pg-edition" content={{ProbGame.edition}}/>}}]

def main := manualMain (%doc ProbGame) (config := config)
