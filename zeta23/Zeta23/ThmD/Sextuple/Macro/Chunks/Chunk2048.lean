import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 67949, payload cursor 33967, depth 16, 1 tokens. -/
theorem chunk2048 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 67949 33967 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (67950, 33968) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
