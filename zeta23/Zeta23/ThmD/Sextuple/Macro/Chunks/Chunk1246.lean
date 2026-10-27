import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 41356, payload cursor 20671, depth 16, 33 tokens. -/
theorem chunk1246 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 41356 20671 (pathBox rootBox [(false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (41389, 20688) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
