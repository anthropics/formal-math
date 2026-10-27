import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 5339, payload cursor 2662, depth 17, 1 tokens. -/
theorem chunk0141 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 5339 2662 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (5340, 2663) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
