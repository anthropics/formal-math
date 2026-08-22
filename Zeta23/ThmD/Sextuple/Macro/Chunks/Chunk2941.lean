import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 98411, payload cursor 49201, depth 11, 83 tokens. -/
theorem chunk2941 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 50 98411 49201 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98494, 49243) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
