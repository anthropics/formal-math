import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 70298, payload cursor 35142, depth 17, 1 tokens. -/
theorem chunk2140 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 70298 35142 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (70299, 35143) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
