import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 68859, payload cursor 34422, depth 21, 1 tokens. -/
theorem chunk2086 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 68859 34422 (pathBox rootBox [(false, 2), (true, 4), (false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (68860, 34423) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
