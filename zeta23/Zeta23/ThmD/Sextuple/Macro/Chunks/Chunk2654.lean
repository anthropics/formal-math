import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 86509, payload cursor 43244, depth 36, 65 tokens. -/
theorem chunk2654 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 25 86509 43244 (pathBox rootBox [(true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (true, 4), (true, 0), (false, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (86574, 43277) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
