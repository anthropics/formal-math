import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 61076, payload cursor 30530, depth 24, 1 tokens. -/
theorem chunk1840 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 37 61076 30530 (pathBox rootBox [(false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (61077, 30531) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
