import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 92209, payload cursor 46099, depth 15, 31 tokens. -/
theorem chunk2842 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 92209 46099 (pathBox rootBox [(true, 4), (false, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (92240, 46115) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
