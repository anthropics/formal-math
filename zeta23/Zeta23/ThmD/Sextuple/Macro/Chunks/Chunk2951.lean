import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 98609, payload cursor 49298, depth 15, 31 tokens. -/
theorem chunk2951 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 98609 49298 (pathBox rootBox [(true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (98640, 49314) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
