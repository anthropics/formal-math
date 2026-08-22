import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 98640, payload cursor 49314, depth 14, 49 tokens. -/
theorem chunk2952 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 47 98640 49314 (pathBox rootBox [(true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (98689, 49339) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
