import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 67705, payload cursor 33846, depth 18, 1 tokens. -/
theorem chunk2042 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 67705 33846 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (67706, 33847) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
