import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 42348, payload cursor 21164, depth 34, 29 tokens. -/
theorem chunk1281 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 27 42348 21164 (pathBox rootBox [(false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (42377, 21179) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
