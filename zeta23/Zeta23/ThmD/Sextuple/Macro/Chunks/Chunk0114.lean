import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 4527, payload cursor 2255, depth 30, 1 tokens. -/
theorem chunk0114 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 31 4527 2255 (pathBox rootBox [(false, 4), (true, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (4528, 2256) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
