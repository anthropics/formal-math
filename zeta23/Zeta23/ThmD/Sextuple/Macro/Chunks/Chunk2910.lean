import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 96476, payload cursor 48234, depth 10, 61 tokens. -/
theorem chunk2910 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 51 96476 48234 (pathBox rootBox [(true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96537, 48265) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
