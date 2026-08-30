import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 18432, payload cursor 9209, depth 19, 1 tokens. -/
theorem chunk0616 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 18432 9209 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (18433, 9210) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
