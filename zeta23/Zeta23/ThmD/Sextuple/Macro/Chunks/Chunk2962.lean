import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 99308, payload cursor 49651, depth 8, 99 tokens. -/
theorem chunk2962 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 53 99308 49651 (pathBox rootBox [(false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (99407, 49701) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
