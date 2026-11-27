import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 80521, payload cursor 40249, depth 37, 55 tokens. -/
theorem chunk2490 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 24 80521 40249 (pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (true, 0), (true, 3), (false, 1), (true, 2), (true, 4), (true, 0), (false, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (80576, 40277) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
