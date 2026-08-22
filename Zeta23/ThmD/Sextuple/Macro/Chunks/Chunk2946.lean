import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 98514, payload cursor 49255, depth 7, 1 tokens. -/
theorem chunk2946 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 54 98514 49255 (pathBox rootBox [(true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98515, 49256) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
