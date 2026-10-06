import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 77976, payload cursor 38980, depth 23, 1 tokens. -/
theorem chunk2391 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 38 77976 38980 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (77977, 38981) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
