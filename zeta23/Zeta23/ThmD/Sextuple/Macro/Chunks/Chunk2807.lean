import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 91000, payload cursor 45494, depth 16, 95 tokens. -/
theorem chunk2807 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 91000 45494 (pathBox rootBox [(true, 2), (true, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (91095, 45542) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
