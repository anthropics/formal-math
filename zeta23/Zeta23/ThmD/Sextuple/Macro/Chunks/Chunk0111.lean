import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 4425, payload cursor 2204, depth 27, 53 tokens. -/
theorem chunk0111 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 34 4425 2204 (pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (4478, 2231) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
