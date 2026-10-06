import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 91221, payload cursor 45605, depth 15, 29 tokens. -/
theorem chunk2810 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 91221 45605 (pathBox rootBox [(true, 4), (true, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (91250, 45620) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
