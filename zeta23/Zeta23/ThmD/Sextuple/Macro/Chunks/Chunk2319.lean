import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 75287, payload cursor 37637, depth 16, 1 tokens. -/
theorem chunk2319 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 75287 37637 (pathBox rootBox [(false, 2), (false, 4), (true, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (75288, 37638) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
