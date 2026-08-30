import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 76379, payload cursor 38183, depth 17, 1 tokens. -/
theorem chunk2356 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 76379 38183 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (76380, 38184) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
