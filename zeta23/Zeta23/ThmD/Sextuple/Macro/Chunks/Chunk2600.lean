import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 84857, payload cursor 42422, depth 15, 95 tokens. -/
theorem chunk2600 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 84857 42422 (pathBox rootBox [(false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (84952, 42470) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
