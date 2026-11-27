import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 67526, payload cursor 33757, depth 16, 91 tokens. -/
theorem chunk2037 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 67526 33757 (pathBox rootBox [(true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (67617, 33803) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
