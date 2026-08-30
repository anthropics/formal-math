import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 96600, payload cursor 48297, depth 8, 69 tokens. -/
theorem chunk2912 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 53 96600 48297 (pathBox rootBox [(true, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96669, 48332) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
