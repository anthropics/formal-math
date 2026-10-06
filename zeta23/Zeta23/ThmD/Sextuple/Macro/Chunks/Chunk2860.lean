import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 93221, payload cursor 46605, depth 14, 59 tokens. -/
theorem chunk2860 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 47 93221 46605 (pathBox rootBox [(true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (93280, 46635) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
