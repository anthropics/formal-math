import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 93441, payload cursor 46716, depth 13, 33 tokens. -/
theorem chunk2863 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 93441 46716 (pathBox rootBox [(true, 3), (true, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (93474, 46733) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
