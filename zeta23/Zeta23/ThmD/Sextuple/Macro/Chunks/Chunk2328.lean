import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 75564, payload cursor 37777, depth 14, 43 tokens. -/
theorem chunk2328 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 47 75564 37777 (pathBox rootBox [(true, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (75607, 37799) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
