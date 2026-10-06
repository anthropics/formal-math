import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 70375, payload cursor 35180, depth 23, 1 tokens. -/
theorem chunk2145 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 38 70375 35180 (pathBox rootBox [(false, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (70376, 35181) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
