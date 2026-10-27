import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 4372, payload cursor 2179, depth 17, 1 tokens. -/
theorem chunk0104 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 4372 2179 (pathBox rootBox [(false, 1), (true, 2), (true, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (4373, 2180) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
