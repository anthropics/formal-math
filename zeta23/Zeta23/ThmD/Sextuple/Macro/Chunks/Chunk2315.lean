import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 75153, payload cursor 37570, depth 22, 25 tokens. -/
theorem chunk2315 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 39 75153 37570 (pathBox rootBox [(true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (75178, 37583) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
