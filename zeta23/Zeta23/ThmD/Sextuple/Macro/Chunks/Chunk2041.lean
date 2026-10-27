import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 67697, payload cursor 33842, depth 17, 7 tokens. -/
theorem chunk2041 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 67697 33842 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (67704, 33846) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
