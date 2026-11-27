import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 71784, payload cursor 35884, depth 19, 1 tokens. -/
theorem chunk2185 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 71784 35884 (pathBox rootBox [(false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (71785, 35885) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
