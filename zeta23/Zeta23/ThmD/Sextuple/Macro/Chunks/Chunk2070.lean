import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 68612, payload cursor 34299, depth 16, 1 tokens. -/
theorem chunk2070 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 68612 34299 (pathBox rootBox [(false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (68613, 34300) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
