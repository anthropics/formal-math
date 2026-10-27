import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 93188, payload cursor 46588, depth 15, 33 tokens. -/
theorem chunk2859 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 93188 46588 (pathBox rootBox [(true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (93221, 46605) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
