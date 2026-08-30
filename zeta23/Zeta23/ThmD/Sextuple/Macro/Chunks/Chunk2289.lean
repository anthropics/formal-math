import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 74280, payload cursor 37132, depth 26, 63 tokens. -/
theorem chunk2289 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 35 74280 37132 (pathBox rootBox [(false, 2), (true, 4), (true, 0), (false, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (74343, 37164) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
