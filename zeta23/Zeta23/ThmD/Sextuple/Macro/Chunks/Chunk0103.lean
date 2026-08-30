import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 4370, payload cursor 2178, depth 16, 1 tokens. -/
theorem chunk0103 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 4370 2178 (pathBox rootBox [(false, 2), (true, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (4371, 2179) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
